import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_25_L_R_L_I_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · rcases h5bigk with h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hc15, hlam, hphi, p14_1, u5elo0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hc25, hlam, hphi, p14_1, u5elo0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h13, hc45, hlam, hphi, p14_1, u5elo0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hc45, hlam, hphi, p14_1, u5elo0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h2, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h11, h13, hc45, hlam, hphi, p14_1, u5elo1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h13, h2, hc45, hlam, hphi, p14_1, u5elo0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h2, hc45, hlam, hphi, p14_1, u5elo0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h3, hlam, p14_1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h6, hlam, p14_1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h13, hc45, hlam, hphi, p14_1, u5elo2]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h0, h12, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p14_1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, ht12, ht23, p14_1, u1ehi4]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h8, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h11, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h0, h11, h12, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p14_1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h4, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h9, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h12, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h13, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hlam, p14_0]
                            · linarith only [h0, h12, h13, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                            · linarith only [h10, h12, h41, hlam]
                            · rcases h5bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [hlam, p43_0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p43_1, u1ehi4, u5elo0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h10, h12, hc34, hlam, hphi, ht45, p43_1, u5elo0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [hc35, hlam, hphi, p43_1, u5elo0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [hc45, hlam, hphi, p43_1, u5elo0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h2, hlam, p43_0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [hlam, p43_0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h10, h12, hc34, hlam, hphi, ht45, p43_1, u5elo1]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, p43_1, u5elo0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h2, hc45, hlam, hphi, p43_1, u5elo0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h3, hlam, p43_1]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h6, hlam, p43_1]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [hlam, p43_0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [hc35, hlam, hphi, p43_1, u5elo2]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h12, hlam, p43_1]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, ht12, ht23, p43_1, u1ehi4]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h8, hlam, p43_0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h11, hlam, p43_0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [hlam, p43_0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h41, hlam, p43_1]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h4, hlam, p43_0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h9, hlam, p43_0]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h0, h5, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p43_1]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [h0, h5, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p43_1]
                              · have p43_0 := h43c.1
                                have p43_1 := h43c.2.1
                                have p43_2 := h43c.2.2.1
                                have p43_3 := h43c.2.2.2
                                linarith only [hlam, p43_0]
                        · linarith only [h10, h11, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
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
                                linarith only [hc15, hlam, hphi, p73_1, u5elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hc25, hlam, hphi, p73_1, u5elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h72, hc45, hlam, hphi, p73_1, u5elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hc45, hlam, hphi, p73_1, u5elo0]
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
                                linarith only [h70, h72, hc45, hlam, hphi, p73_1, u5elo1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h2, h72, hc45, hlam, hphi, p73_1, u5elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h2, hc45, hlam, hphi, p73_1, u5elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h3, hlam, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h6, hlam, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h72, hc45, hlam, hphi, p73_1, u5elo2]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hc45, hlam, hphi, p73_1, u5elo2]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, ht12, ht23, p73_1, u1ehi4]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h8, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h70, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h0, h10, h5, h7, h70, hc01, hc45, hlam, hphi, ht0b, ht5b, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h4, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h9, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h71, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h72, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                            · linarith only [h10, h72, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h0, h10, h5, h70, h71, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h101 | h101
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h102 | h102
                            · rcases h5bigk with h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p103_1, u1ehi4, u5elo0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hc25, hlam, hphi, p103_1, u5elo0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hc35, hlam, hphi, p103_1, u5elo0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hc45, hlam, hphi, p103_1, u5elo0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h2, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h70, hc23, hlam, hphi, ht34, ht45, p103_1, u5elo1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, p103_1, u5elo0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h2, hc45, hlam, hphi, p103_1, u5elo0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h3, hlam, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h6, hlam, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h70, hlam, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hc45, hlam, hphi, p103_1, u5elo2]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, ht12, ht23, p103_1, u1ehi4]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h8, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h2, h8, hc25, hlam, hphi, p103_1, u5elo0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h2, h8, hc45, hlam, hphi, p103_1, u5elo0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h4, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h9, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h101, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h102, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                            · linarith only [h10, h102, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                            · rcases h5bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hc15, hlam, hphi, p131_1, u5elo0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h10, h101, hc23, hlam, hphi, ht34, ht45, p131_1, u5elo0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h10, h101, h130, hc23, hlam, hphi, ht34, ht45, p131_1, u5elo0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h10, h101, hc23, hlam, hphi, ht34, ht45, p131_1, u5elo0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h2, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h10, h101, hc23, hlam, hphi, ht34, ht45, p131_1, u5elo1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h10, h101, h130, h2, hc23, hlam, hphi, ht34, ht45, p131_1, u5elo0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h10, h101, h2, hc23, hlam, hphi, ht34, ht45, p131_1, u5elo0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h3, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h6, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h70, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h101, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, ht12, ht23, p131_1, u1ehi4]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h8, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h10, h101, h2, h8, hc23, hlam, hphi, ht34, ht45, p131_1, u5elo0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h10, h101, h2, h8, hc23, hlam, hphi, ht34, ht45, p131_1, u5elo0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h4, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h9, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h10, h101, h130, hc23, hc34, hlam, hphi, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h130, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                            · linarith only [h0, h10, h130, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h9, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                  · linarith only [h8, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                      · linarith only [h160, h162, h7, hc23, hlam, hphi, ht12, u1ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h165 | h165
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h166 | h166
                            · rcases h5bigk with h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p167_1, u1ehi4, u5elo0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [hc25, hlam, hphi, p167_1, u5elo0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h166, hc45, hlam, hphi, p167_1, u5elo0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [hc45, hlam, hphi, p167_1, u5elo0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h2, hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h164, h166, hc45, hlam, hphi, p167_1, u5elo1]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h166, h2, hc45, hlam, hphi, p167_1, u5elo0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h2, hc45, hlam, hphi, p167_1, u5elo0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h3, hlam, p167_1]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h6, hlam, p167_1]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h166, hc45, hlam, hphi, p167_1, u5elo2]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h0, h162, h164, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p167_1]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, ht12, ht23, p167_1, u1ehi4]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h160, hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h164, hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h0, h162, h164, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p167_1]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h4, hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h161, hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h165, hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [h166, hlam, p167_0]
                              · have p167_0 := h167c.1
                                have p167_1 := h167c.2.1
                                have p167_2 := h167c.2.2.1
                                have p167_3 := h167c.2.2.2
                                linarith only [hlam, p167_0]
                            · linarith only [h160, h166, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                          · linarith only [h162, h164, h165, hc35, hlam, hphi, u5elo4]
                        · linarith only [h160, h164, h7, hc23, hc34, hlam, hphi]
                    · linarith only [h161, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                  · linarith only [h160, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
              · linarith only [h6, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h199 | h199
              · rcases m.htr 1 3 4 (by decide) (by decide) with h200 | h200
                · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h205 | h205
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                            · rcases h5bigk with h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p207_1, u1ehi4, u5elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hc25, hlam, hphi, p207_1, u5elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h206, hc45, hlam, hphi, p207_1, u5elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hc45, hlam, hphi, p207_1, u5elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h2, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h204, h206, hc45, hlam, hphi, p207_1, u5elo1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h2, h206, hc45, hlam, hphi, p207_1, u5elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h2, hc45, hlam, hphi, p207_1, u5elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h3, hlam, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h199, hlam, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h206, hc45, hlam, hphi, p207_1, u5elo2]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h199, h203, h5, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, ht12, ht23, p207_1, u1ehi4]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h201, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h204, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h199, h203, h204, h5, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h4, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h202, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h205, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h206, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                            · rcases h5bigk with h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p233_1, u1ehi4, u5elo0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hc25, hlam, hphi, p233_1, u5elo0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h206, hc34, hlam, hphi, ht45, p233_1, u5elo0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h206, hc34, hlam, hphi, ht45, p233_1, u5elo0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h2, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h205, h206, hc34, hlam, hphi, ht45, p233_1, u5elo1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h2, h206, hc34, hlam, hphi, ht45, p233_1, u5elo0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h2, h206, hc34, hlam, hphi, ht45, p233_1, u5elo0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h3, hlam, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h199, hlam, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h199, h203, h206, h5, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h199, h203, h206, h5, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, ht12, ht23, p233_1, u1ehi4]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h201, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h204, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h206, hlam, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h4, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h202, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h205, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hc35, hlam, hphi, p233_1, u5elo4]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, p233_0]
                          · linarith only [h199, h200, h202, h205, h5, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h203, h204, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h199, h200, h203, h5, hc13, hlam, hphi, u1ehi4]
                    · linarith only [h202, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                  · linarith only [h201, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h264 | h264
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h265 | h265
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h266 | h266
                      · linarith only [h200, h264, h266, hc23, hlam, hphi, ht12, u1ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h268 | h268
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h269 | h269
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h270 | h270
                            · rcases h5bigk with h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p271_1, u1ehi4, u5elo0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h268, h270, hc45, hlam, hphi, p271_1, u5elo0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h270, hc45, hlam, hphi, p271_1, u5elo0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hc45, hlam, hphi, p271_1, u5elo0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h2, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h268, h270, hc45, hlam, hphi, p271_1, u5elo1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h2, h270, hc45, hlam, hphi, p271_1, u5elo0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h2, hc45, hlam, hphi, p271_1, u5elo0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h3, hlam, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h199, hlam, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h270, hc45, hlam, hphi, p271_1, u5elo2]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h199, h5, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h2, hc35, hlam, hphi, ht12, ht23, p271_1, u1ehi4]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h264, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h268, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h199, h266, h268, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h4, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h265, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h269, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h270, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, p271_0]
                            · linarith only [h266, h270, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                          · linarith only [h199, h265, h269, h5, hc14, hlam, hphi, u1ehi4]
                        · linarith only [h200, h264, h268, hc23, hc34, hlam, hphi]
                    · linarith only [h265, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                  · linarith only [h264, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
              · linarith only [h199, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
          · linarith only [h1, h4, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
        · linarith only [h0, h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h307 | h307
    · linarith only [h0, h307, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h309 | h309
      · linarith only [h0, h309, hc12, hlam, hphi, u1ehi4]
      · linarith only [h309, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_12_13_25_L_I_L_R_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h5, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · linarith only [h9, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h4, h6, hlam, hphi, ht34, ht45, u3ehi1, u5elo2]
            · linarith only [h0, h2, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
              · linarith only [h0, h1, h15, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h14, h15, h3, hc24, hlam, hphi, ht45, u5elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
              · linarith only [h0, h14, h18, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h1, h20, h22, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · linarith only [h22, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h21, h4, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                  · linarith only [h20, h26, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h26, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
        · linarith only [h1, h3, hlam, hphi, ht34, ht45, u3ehi0, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h30 | h30
        · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
            · linarith only [h0, h2, h32, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
              · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                · linarith only [h0, h2, h31, h35, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h2, h31, h35, hc34, hlam, hphi, u3ehi2]
              · linarith only [h31, h34, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
          · linarith only [h1, h2, h31, hc12, hc24, hlam, hphi]
        · linarith only [h1, h30, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h41 | h41
      · rcases m.htr 0 2 5 (by decide) (by decide) with h42 | h42
        · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
          · linarith only [h1, h42, h43, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
              · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h0, h1, h45, h47, h49, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h49, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h0, h1, h45, h48, hc24, hlam, hphi, ht45, u5elo3]
                · linarith only [h0, h1, h46, h47, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · linarith only [h45, h46, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h1, h41, h45, hc12, hc23, hlam, hphi]
        · linarith only [h41, h42, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h57 | h57
        · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
          · linarith only [h0, h1, h58, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
            · linarith only [h0, h41, h60, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h62 | h62
              · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                    · rcases h2bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h41, h62, h63, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u3ehi4]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h1, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h41, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h41, h63, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u3ehi4]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h58, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h60, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, h64, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p66_1, u3ehi4]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h57, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u3ehi4]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h62, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u3ehi4]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h41, h57, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u3ehi4]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        rcases p66_3 (m.d 0 2) (by simp) with h81 | h81
                        · linarith only [h1, h81, hlam]
                        · linarith only [h57, h81, hlam]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, h62, h64, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u3ehi4]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h62, h64, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u3ehi4]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h63, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        rcases p66_3 (m.d 0 2) (by simp) with h88 | h88
                        · linarith only [h41, h88, hlam]
                        · linarith only [h57, h88, hlam]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h57, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h62, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h64, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hc24, hlam, hphi, ht45, p66_1, u5elo2]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                    · linarith only [h65, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h0, h41, h62, h63, h64, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h0, h1, h62, h63, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · linarith only [h1, h57, h62, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h100 | h100
          · linarith only [h0, h1, h100, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
            · linarith only [h0, h102, h41, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
              · linarith only [h0, h104, h57, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                    · rcases h2bigk with h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h57, hc12, hlam, hphi, ht23, ht34, ht45, p109_1, u5elo2]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h1, hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h41, hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h57, hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h0, hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h100, hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h102, hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h104, hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        rcases p109_3 (m.d 0 2) (by simp) with h120 | h120
                        · linarith only [h120, hlam, p109_0]
                        · rcases p109_3 (m.d 1 2) (by simp) with h122 | h122
                          · linarith only [h100, h122, hlam]
                          · rcases p109_3 (m.d 2 3) (by simp) with h124 | h124
                            · rcases p109_3 (m.d 2 4) (by simp) with h125 | h125
                              · linarith only [h106, h125, hlam]
                              · linarith only [h125, h41, hlam]
                            · linarith only [h124, hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        rcases p109_3 (m.d 0 2) (by simp) with h129 | h129
                        · linarith only [h1, h129, hlam]
                        · linarith only [h0, h129, hlam]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h106, h108, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p109_1, u5ehi9]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h57, hc02, hc23, hlam, hphi, p109_1]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        rcases p109_3 (m.d 0 2) (by simp) with h135 | h135
                        · linarith only [h135, hlam, p109_0]
                        · rcases p109_3 (m.d 1 2) (by simp) with h137 | h137
                          · linarith only [h102, h137, hlam]
                          · rcases p109_3 (m.d 2 3) (by simp) with h139 | h139
                            · rcases p109_3 (m.d 2 4) (by simp) with h140 | h140
                              · rcases p109_3 (m.d 2 5) (by simp) with h141 | h141
                                · linarith only [h0, h141, hc12, hlam, hphi, ht23, ht34, ht45, p109_1, u5elo2]
                                · linarith only [h141, h57, hlam]
                              · linarith only [h140, hlam, p109_0]
                            · linarith only [h1, h139, hlam]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        rcases p109_3 (m.d 0 2) (by simp) with h146 | h146
                        · linarith only [h146, h41, hlam]
                        · linarith only [h0, h146, hlam]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h106, hlam, p109_1]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [hlam, p109_0]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h0, h57, hc12, hc24, hlam, hphi, p109_1]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p109_1, u5elo2]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p109_1, u5elo2]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [h107, hlam, p109_1]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [hc24, hlam, hphi, ht45, p109_1, u5elo2]
                      · have p109_0 := h109c.1
                        have p109_1 := h109c.2.1
                        have p109_2 := h109c.2.2.1
                        have p109_3 := h109c.2.2.2
                        linarith only [hlam, p109_0]
                    · linarith only [h108, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h107, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h159 | h159
                  · linarith only [h106, h159, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h159, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h162 | h162
    · rcases m.htr 0 2 4 (by decide) (by decide) with h163 | h163
      · rcases m.htr 0 2 5 (by decide) (by decide) with h164 | h164
        · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
          · rcases m.htr 1 2 4 (by decide) (by decide) with h166 | h166
            · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
              · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                · rcases m.htr 2 3 5 (by decide) (by decide) with h169 | h169
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h170 | h170
                    · linarith only [h162, h168, h170, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · linarith only [h170, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h168, h169, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                  · linarith only [h168, h174, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h174, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h0, h164, h167, hlam]
            · linarith only [h0, h163, h166, hlam]
          · linarith only [h0, h162, h165, hlam]
        · linarith only [h162, h164, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h181 | h181
        · rcases m.htr 1 2 3 (by decide) (by decide) with h182 | h182
          · rcases m.htr 1 2 4 (by decide) (by decide) with h183 | h183
            · linarith only [h162, h163, h183, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
              · rcases m.htr 2 3 4 (by decide) (by decide) with h186 | h186
                · linarith only [h0, h162, h183, h186, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h162, h183, h186, hc34, hlam, hphi, u3ehi2]
              · linarith only [h0, h181, h185, hlam]
          · linarith only [h0, h162, h182, hlam]
        · linarith only [h162, h181, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h192 | h192
      · rcases m.htr 0 2 5 (by decide) (by decide) with h193 | h193
        · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
          · linarith only [h162, h193, h194, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
            · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
              · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h200 | h200
                    · linarith only [h0, h192, h194, h198, h200, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h200, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h0, h194, h199, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h194, h198, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h193, h197, hlam]
            · linarith only [h0, h192, h196, hlam]
        · linarith only [h192, h193, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h208 | h208
        · rcases m.htr 1 2 3 (by decide) (by decide) with h209 | h209
          · linarith only [h162, h208, h209, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
            · linarith only [h192, h208, h211, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
              · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                · rcases m.htr 2 3 5 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h216 | h216
                    · rcases h2bigk with h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, hlam, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h162, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h192, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h211, h214, h215, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p217_1, u3ehi4]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h211, h214, hc02, hc23, hlam, hphi, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h209, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h211, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h211, h214, h215, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p217_1, u3ehi4]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h208, h215, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p217_1, u3ehi4]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h192, h208, h215, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p217_1, u3ehi4]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        rcases p217_3 (m.d 0 2) (by simp) with h232 | h232
                        · linarith only [h162, h232, hlam]
                        · linarith only [h208, h232, hlam]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h208, h215, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p217_1, u3ehi4]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h208, h215, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p217_1, u3ehi4]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h214, hlam, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        rcases p217_3 (m.d 0 2) (by simp) with h239 | h239
                        · linarith only [h192, h239, hlam]
                        · linarith only [h208, h239, hlam]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h208, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h213, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h215, hlam, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hc24, hlam, hphi, ht45, p217_1, u5elo2]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                    · linarith only [h216, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h162, h215, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
                · linarith only [h0, h208, h209, h214, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · linarith only [h0, h208, h213, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
          · rcases m.htr 1 2 4 (by decide) (by decide) with h252 | h252
            · rcases m.htr 1 2 5 (by decide) (by decide) with h253 | h253
              · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
                · rcases m.htr 2 3 5 (by decide) (by decide) with h255 | h255
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h256 | h256
                    · linarith only [h251, h254, h256, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h256, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h255, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                  · linarith only [h254, h260, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h162, h260, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h253, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h162, h251, h252, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h265 | h265
            · linarith only [h0, h192, h251, h265, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
              · linarith only [h0, h208, h251, h267, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h267, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

end R2N4
