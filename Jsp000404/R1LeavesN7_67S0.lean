import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_14_25_L_0_L_0_H_I_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
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
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                                  · linarith only [h0, h14, h17, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h17, h7, hc34, hlam, hphi, u4elo0]
                                · linarith only [h13, h16, hc24, hlam, hphi, u4elo1]
                              · linarith only [h1, h12, h14, h15, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                              · linarith only [h14, h22, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                                  · rcases h5bigk with h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [hlam, p26_0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h1, h11, h22, h25, h3, h7, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p26_1, u2elo0, u4elo0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h1, h11, h22, h25, h3, h7, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p26_1, u2elo0, u4elo0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h22, h7, hc23, hlam, hphi, ht34, p26_1, u4elo0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h1, h11, h22, h25, h3, h7, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p26_1, u2elo0, u4elo0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h2, hlam, p26_0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [hlam, p26_0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p26_1]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h2, h22, h7, hc23, hlam, hphi, ht34, p26_1, u4elo0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h1, h11, h2, h22, h25, h3, h7, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p26_1, u2elo0, u4elo0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h4, hlam, p26_1]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h10, hlam, p26_1]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [hlam, p26_0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h22, hlam, p26_1]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p26_1, u2elo4]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h6, hlam, p26_1]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h12, hlam, p26_1]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h1, h11, h25, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p26_1, u2elo0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [hlam, p26_0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h1, h11, h25, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p26_1, u2elo0]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h7, hlam, p26_1]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h13, hlam, p26_1]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h24, hlam, p26_1]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [h25, hlam, p26_1]
                                    · have p26_0 := h26c.1
                                      have p26_1 := h26c.2.1
                                      have p26_2 := h26c.2.2.1
                                      have p26_3 := h26c.2.2.2
                                      linarith only [hlam, p26_0]
                                  · linarith only [h14, h25, h7, hc24, hlam, hphi, u4elo0]
                                · linarith only [h14, h24, h7, hc23, hlam, hphi, ht34, u4elo0]
                          · linarith only [h13, h7, hc14, hlam, hphi, u4elo0]
                        · linarith only [h11, h12, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                        · linarith only [h11, h3, h5, h56, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                            · linarith only [h11, h3, h59, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                              · linarith only [h11, h3, h5, h61, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                                  · rcases h5bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [hlam, p65_0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h3, h5, h56, h64, h7, h8, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p65_1, u2elo0, u4elo0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h3, h5, h56, h64, h7, h8, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p65_1, u2elo0, u4elo0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h56, h7, h8, hc23, hlam, hphi, ht34, p65_1, u4elo0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h3, h5, h56, h64, h7, h8, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p65_1, u2elo0, u4elo0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h2, hlam, p65_0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [hlam, p65_0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p65_1]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h56, hlam, p65_0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h3, h5, h56, h64, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p65_1, u2elo0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h4, hlam, p65_1]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h10, hlam, p65_1]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [hlam, p65_0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h61, hlam, p65_1]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p65_1, u2elo4]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h6, hlam, p65_1]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h3, h5, h64, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p65_1, u2elo0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h3, h5, h64, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p65_1, u2elo0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [hlam, p65_0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h3, h5, h64, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p65_1, u2elo0]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h7, hlam, p65_1]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h58, hlam, p65_1]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h63, hlam, p65_1]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [h64, hlam, p65_1]
                                    · have p65_0 := h65c.1
                                      have p65_1 := h65c.2.1
                                      have p65_2 := h65c.2.2.1
                                      have p65_3 := h65c.2.2.2
                                      linarith only [hlam, p65_0]
                                  · linarith only [h63, h64, h9, hc34, hlam, hphi, u4elo1]
                                · linarith only [h58, h63, hc24, hlam, hphi, u4elo1]
                          · linarith only [h58, h7, hc14, hlam, hphi, u4elo0]
                    · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h8, h9, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
                · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h101 | h101
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                          · linarith only [h102, h7, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                                · linarith only [h106, h5, h7, h98, hc34, hlam, hphi, u4elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                                  · linarith only [h102, h108, h5, hc14, hlam, hphi, u4elo0]
                                  · rcases h5bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [hlam, p110_0]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p110_1, u4elo4]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h106, h7, hc24, hlam, hphi, p110_1, u4elo4]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p110_1, u4elo4]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h7, hlam, p110_0]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h2, hlam, p110_0]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [hlam, p110_0]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h106, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p110_1]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h1, h101, hc01, hc35, hlam, hphi, ht0b, ht5b, p110_1]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h102, hlam, p110_0]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h4, hlam, p110_1]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h99, hlam, p110_1]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [hlam, p110_0]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo4]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h106, hlam, p110_0]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h6, hlam, p110_1]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h101, hlam, p110_1]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h105, hlam, p110_0]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [hlam, p110_0]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h108, hlam, p110_0]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p110_1, u4elo4]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p110_1, u4elo4]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [h105, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p110_1, u4elo4]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p110_1, u4elo4]
                                    · have p110_0 := h110c.1
                                      have p110_1 := h110c.2.1
                                      have p110_2 := h110c.2.2.1
                                      have p110_3 := h110c.2.2.2
                                      linarith only [hlam, p110_0]
                              · linarith only [h1, h101, h104, h105, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · linarith only [h104, h5, h7, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h100, h101, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h100, h5, h7, hc13, hlam, hphi, ht34, u4elo4]
                    · linarith only [h4, h99, hc12, hlam, hphi, u2elo0]
                  · linarith only [h97, h98, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h3, h97, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h143 | h143
              · linarith only [h143, h5, h6, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
                · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
                        · linarith only [h1, h149, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h151 | h151
                          · linarith only [h143, h151, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h154 | h154
                              · linarith only [h1, h145, h154, h6, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                                · linarith only [h151, h156, hc14, hlam, hphi, u4elo2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                                  · linarith only [h0, h147, h151, h153, h154, h158, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h153, h158, h3, h6, hc34, hlam, hphi, u4elo4]
                            · linarith only [h153, h5, h6, hc23, hc35, hlam, hphi]
                      · linarith only [h143, h145, h148, h5, h6, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h147, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h145, h146, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h145, h3, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
            · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
              · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                      · linarith only [h1, h166, h171, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h174 | h174
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                            · linarith only [h1, h168, h173, h175, h5, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h179 | h179
                                  · rcases h5bigk with h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h166, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p180_1, u4elo3]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h166, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p180_1, u4elo3]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h166, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p180_1, u4elo3]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h166, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p180_1, u4elo3]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h2, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h166, h179, h2, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p180_1, u4elo3]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h166, h2, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p180_1, u4elo3]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h4, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h170, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h179, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p180_1, u2elo4]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h166, h170, h2, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p180_1, u4elo3]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h166, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h173, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h177, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h166, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p180_1, u4elo3]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h167, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h174, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h178, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h179, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hlam, p180_0]
                                  · linarith only [h179, h5, hc03, hlam, hphi, ht34, u4elo4]
                                · linarith only [h174, h178, hc24, hlam, hphi, u4elo1]
                              · linarith only [h166, h177, h5, hc23, hlam, hphi, ht34, u4elo3]
                          · linarith only [h167, h174, h5, hc14, hlam, hphi, u4elo3]
                        · linarith only [h166, h173, h5, hc13, hlam, hphi, ht34, u4elo3]
                    · linarith only [h170, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h168, h169, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h168, h3, hc12, hlam, hphi, u2elo0]
              · linarith only [h166, h167, h5, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
              · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
                · rcases m.htr 1 2 4 (by decide) (by decide) with h217 | h217
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h218 | h218
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                      · linarith only [h1, h219, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h221 | h221
                        · linarith only [h1, h166, h221, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h223 | h223
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                            · linarith only [h224, h3, h5, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                              · linarith only [h1, h166, h216, h226, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                                  · rcases h5bigk with h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [hlam, p230_0]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h216, h221, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p230_1, u2elo0]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h226, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p230_1, u2elo0]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h166, hlam, p230_0]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h215, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p230_1, u4elo0]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h2, hlam, p230_0]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [hlam, p230_0]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h2, h226, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h221, hlam, p230_0]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h2, h215, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p230_1, u4elo3]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h4, hlam, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h218, hlam, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [hlam, p230_0]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h226, hlam, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p230_1, u2elo4]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h1, h166, h216, hc23, hc35, hlam, hphi, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h216, h221, hc23, hc35, hlam, hphi, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h226, hc23, hc35, hlam, hphi, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [hlam, p230_0]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h229, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p230_1, u4elo3]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h215, hlam, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h223, hlam, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h228, hlam, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [h229, hlam, p230_1]
                                    · have p230_0 := h230c.1
                                      have p230_1 := h230c.2.1
                                      have p230_2 := h230c.2.2.1
                                      have p230_3 := h230c.2.2.2
                                      linarith only [hlam, p230_0]
                                  · linarith only [h217, h228, h229, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · linarith only [h215, h228, h5, hc24, hlam, hphi, u4elo3]
                          · linarith only [h215, h223, h5, hc14, hlam, hphi, u4elo3]
                    · linarith only [h218, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h216, h217, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h216, h3, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
                · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h264 | h264
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h265 | h265
                      · linarith only [h1, h265, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
                        · linarith only [h1, h166, h267, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                          · linarith only [h215, h269, h5, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h271 | h271
                            · linarith only [h1, h262, h271, h5, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h273 | h273
                              · linarith only [h1, h166, h262, h273, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h275 | h275
                                · linarith only [h1, h215, h262, h263, h275, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                                  · linarith only [h1, h215, h262, h277, h5, hc23, hlam, hphi, ht34, u4elo3]
                                  · linarith only [h1, h262, h277, h5, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h264, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h262, h263, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h262, h3, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h283 | h283
          · rcases m.htr 0 3 5 (by decide) (by decide) with h284 | h284
            · linarith only [h284, h3, h4, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
              · linarith only [h283, h286, h3, h4, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
                · rcases m.htr 1 2 4 (by decide) (by decide) with h289 | h289
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h290 | h290
                    · linarith only [h290, h4, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h292 | h292
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h293 | h293
                        · linarith only [h0, h284, h288, h293, h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                          · linarith only [h286, h295, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h297 | h297
                            · linarith only [h297, h3, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                            · linarith only [h1, h284, h292, h297, hc23, hc35, hlam, hphi]
                      · linarith only [h283, h292, h3, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h288, h289, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h288, h3, h4, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h303 | h303
            · linarith only [h283, h3, h303, h4, hc23, hlam, hphi, ht34, u4elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h305 | h305
              · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
                · rcases m.htr 1 2 4 (by decide) (by decide) with h307 | h307
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h308 | h308
                    · linarith only [h0, h308, h4, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h310 | h310
                      · linarith only [h1, h283, h310, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h312 | h312
                        · linarith only [h1, h303, h312, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h314 | h314
                          · linarith only [h307, h308, h314, hlam]
                          · linarith only [h305, h314, hc14, hlam, hphi, u4elo0]
                  · linarith only [h306, h307, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h3, h306, h4, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h319 | h319
                · rcases m.htr 1 2 4 (by decide) (by decide) with h320 | h320
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h321 | h321
                    · linarith only [h0, h321, h4, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h323 | h323
                      · linarith only [h1, h283, h305, h323, hc34, hlam, hphi, u4elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h325 | h325
                        · linarith only [h1, h2, h283, h303, h305, h319, h321, h325, hc23, hlam, hphi, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h327 | h327
                          · linarith only [h283, h305, h327, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h329 | h329
                            · linarith only [h1, h283, h319, h329, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                              · linarith only [h0, h303, h320, h329, h331, h4, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h333 | h333
                                · linarith only [h0, h320, h327, h333, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                                · linarith only [h0, h320, h329, h333, h4, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h319, h320, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h3, h319, h4, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h338 | h338
        · rcases m.htr 0 3 4 (by decide) (by decide) with h339 | h339
          · rcases m.htr 0 3 5 (by decide) (by decide) with h340 | h340
            · rcases m.htr 0 4 5 (by decide) (by decide) with h341 | h341
              · rcases m.htr 1 2 3 (by decide) (by decide) with h342 | h342
                · linarith only [h3, h342, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h344 | h344
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h345 | h345
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h346 | h346
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h347 | h347
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h348 | h348
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h350 | h350
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h351 | h351
                                · linarith only [h0, h3, h344, h351, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                                · linarith only [h341, h351, hc24, hlam, hphi, u4elo0]
                              · linarith only [h0, h3, h340, h344, h349, h350, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h1, h3, h342, h344, h349, hc24, hlam, hphi, u4elo3]
                          · linarith only [h341, h348, hc14, hlam, hphi, u4elo0]
                        · linarith only [h3, h340, h342, h344, h347, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h342, h344, h346, hc24, hlam, hphi, u4elo3]
                    · linarith only [h3, h338, h344, h345, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h361 | h361
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h362 | h362
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h366 | h366
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
                                  · rcases h5bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h3, h338, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p368_1, u2elo2]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h3, h338, h365, h367, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p368_1, u2elo2]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h3, h338, h367, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p368_1, u2elo2]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h3, h338, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p368_1, u2elo2]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h2, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h2, h365, h367, hc01, hc45, hlam, hphi, ht0b, ht5b, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h344, h360, h367, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p368_1, u4elo2]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h344, h360, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p368_1, u4elo2]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h338, hlam, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h360, hlam, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h367, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p368_1, u2elo4]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h344, h360, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p368_1, u4elo2]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h340, hlam, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h362, hlam, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h365, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h3, h340, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p368_1, u2elo2]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h341, hlam, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h363, hlam, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h366, hlam, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h367, hlam, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [hlam, p368_0]
                                  · linarith only [h341, h367, hc34, hlam, hphi, u4elo0]
                                · linarith only [h344, h360, h361, h363, h366, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h3, h340, h365, hlam]
                            · linarith only [h3, h364, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h341, h363, hc14, hlam, hphi, u4elo0]
                        · linarith only [h3, h340, h361, h362, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h3, h339, h342, h360, h361, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h338, h360, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h402 | h402
                · linarith only [h3, h402, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                          · linarith only [h341, h408, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h410 | h410
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h411 | h411
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h412 | h412
                                · linarith only [h0, h3, h404, h408, h412, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
                                  · linarith only [h0, h3, h341, h405, h410, h412, h414, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
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
                                      linarith only [h3, h338, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p416_1, u2elo2]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h3, h338, h410, h412, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p416_1, u2elo2]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h3, h338, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p416_1, u2elo2]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h341, hlam, p416_0]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h2, hlam, p416_0]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [hlam, p416_0]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h2, h410, h412, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p416_1]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h2, h3, h338, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p416_1, u2elo2]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h408, hlam, p416_0]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h338, hlam, p416_1]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h405, hlam, p416_1]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [hlam, p416_0]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p416_1, u2elo4]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h412, hlam, p416_0]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h340, hlam, p416_1]
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
                                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p416_1, u4elo4]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h0, h3, h404, h410, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht5b, p416_1, u2elo2, u4elo4]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h0, h3, h404, h410, h411, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p416_1, u2elo2, u4elo4]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [h0, h3, h405, h410, h412, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p416_1, u2elo2, u4elo4]
                                    · have p416_0 := h416c.1
                                      have p416_1 := h416c.2.1
                                      have p416_2 := h416c.2.2.1
                                      have p416_3 := h416c.2.2.2
                                      linarith only [hlam, p416_0]
                              · linarith only [h0, h3, h340, h405, h411, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1, h3, h339, h402, h404, h410, hc24, hlam, hphi, u4elo0]
                        · linarith only [h3, h340, h402, h404, h407, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h402, h404, h406, hc24, hlam, hphi, u4elo3]
                    · linarith only [h3, h338, h404, h405, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h448 | h448
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h449 | h449
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h450 | h450
                          · linarith only [h341, h450, hc04, hlam, hphi, u4elo1]
                          · linarith only [h404, h447, h450, hlam]
                        · linarith only [h3, h340, h404, h448, h449, hc12, hlam, hphi, u2elo2]
                      · linarith only [h3, h339, h402, h447, h448, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h338, h447, hc12, hlam, hphi, u2elo0]
            · linarith only [h3, h338, h340, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h457 | h457
            · rcases m.htr 0 4 5 (by decide) (by decide) with h458 | h458
              · rcases m.htr 1 2 3 (by decide) (by decide) with h459 | h459
                · linarith only [h3, h459, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h461 | h461
                  · linarith only [h0, h3, h339, h461, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h463 | h463
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h464 | h464
                      · linarith only [h1, h339, h464, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h466 | h466
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h467 | h467
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h468 | h468
                            · linarith only [h3, h339, h468, hc02, hlam, hphi, u2elo2]
                            · linarith only [h0, h3, h463, h468, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h458, h459, h463, h464, h467, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                        · linarith only [h3, h457, h459, h463, h466, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h338, h463, hc12, hlam, hphi, u2elo0]
              · linarith only [h3, h338, h339, h458, hlam]
            · linarith only [h3, h338, h457, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h476 | h476
          · rcases m.htr 0 3 5 (by decide) (by decide) with h477 | h477
            · rcases m.htr 0 4 5 (by decide) (by decide) with h478 | h478
              · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
                · linarith only [h3, h479, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h481 | h481
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h482 | h482
                    · linarith only [h0, h338, h482, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h484 | h484
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h485 | h485
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h486 | h486
                          · linarith only [h481, h482, h486, hlam]
                          · linarith only [h478, h486, hc14, hlam, hphi, u4elo0]
                        · linarith only [h3, h477, h484, h485, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h479, h481, h484, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h491 | h491
                    · linarith only [h338, h481, h491, hc02, hlam, hphi, ht23, ht34, u4elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h494 | h494
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h495 | h495
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h496 | h496
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h497 | h497
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h498 | h498
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h499 | h499
                                  · rcases h5bigk with h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [hlam, p500_0]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h338, h498, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo2]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h338, hlam, p500_0]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h338, h498, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo2]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h338, h498, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo2]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h2, hlam, p500_0]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [hlam, p500_0]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h491, hlam, p500_0]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p500_1]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h2, h338, h498, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo2]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h498, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo2]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h498, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo2]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [hlam, p500_0]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h498, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo2]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h498, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo2]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h477, hlam, p500_1]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h494, hlam, p500_1]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h497, hlam, p500_0]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [hlam, p500_0]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h477, hc03, hc45, hlam, hphi, ht0b, ht5b, p500_1]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h478, hlam, p500_1]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h495, hlam, p500_1]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h498, hlam, p500_1]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [h499, hlam, p500_1]
                                    · have p500_0 := h500c.1
                                      have p500_1 := h500c.2.1
                                      have p500_2 := h500c.2.2.1
                                      have p500_3 := h500c.2.2.2
                                      linarith only [hlam, p500_0]
                                  · linarith only [h478, h499, hc34, hlam, hphi, u4elo0]
                                · linarith only [h495, h498, hc24, hlam, hphi, u4elo1]
                              · linarith only [h1, h3, h494, h497, hlam]
                            · linarith only [h0, h3, h496, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h478, h495, hc14, hlam, hphi, u4elo0]
                        · linarith only [h3, h477, h479, h494, hc12, hlam, hphi, u2elo2]
                      · linarith only [h3, h476, h479, h493, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
                · linarith only [h0, h3, h338, h477, h533, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h535 | h535
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h536 | h536
                    · linarith only [h0, h338, h536, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h538 | h538
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h539 | h539
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h540 | h540
                          · linarith only [h478, h540, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h542 | h542
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h543 | h543
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h544 | h544
                                · linarith only [h0, h338, h535, h540, h543, h544, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                                · linarith only [h0, h338, h535, h542, h544, hc34, hlam, hphi, u4elo4]
                              · linarith only [h1, h3, h539, h543, hlam]
                            · linarith only [h3, h476, h542, hc02, hlam, hphi, ht23, ht34, u4elo0]
                        · linarith only [h3, h477, h533, h535, h539, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h533, h535, h538, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h551 | h551
                    · linarith only [h338, h535, h551, hc02, hlam, hphi, ht23, ht34, u4elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h553 | h553
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h554 | h554
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h555 | h555
                          · linarith only [h478, h555, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h557 | h557
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h558 | h558
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h559 | h559
                                · linarith only [h535, h555, h559, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h535, h559, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h0, h2, h3, h338, h554, h558, hc12, hlam, hphi, u2elo4]
                            · linarith only [h0, h3, h476, h557, hc12, hlam, hphi, ht23, ht34, u4elo0]
                        · linarith only [h3, h477, h553, h554, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h3, h476, h533, h553, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h566 | h566
              · linarith only [h476, h477, h566, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
                · linarith only [h0, h3, h568, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h570 | h570
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h571 | h571
                    · linarith only [h0, h338, h571, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h573 | h573
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h574 | h574
                        · linarith only [h1, h477, h574, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h576 | h576
                          · linarith only [h566, h576, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h579 | h579
                              · linarith only [h0, h3, h477, h570, h578, h579, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h581 | h581
                                · linarith only [h0, h570, h576, h581, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                · linarith only [h0, h3, h570, h578, h579, h581, hc34, hlam, hphi, u4elo4]
                            · linarith only [h3, h476, h578, hc02, hlam, hphi, ht23, ht34, u4elo0]
                      · linarith only [h476, h477, h566, h573, hc13, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h586 | h586
                    · linarith only [h338, h570, h586, hc02, hlam, hphi, ht23, ht34, u4elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h588 | h588
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h589 | h589
                        · linarith only [h1, h477, h589, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h591 | h591
                          · linarith only [h566, h591, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h593 | h593
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h594 | h594
                              · linarith only [h1, h477, h588, h594, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h596 | h596
                                · linarith only [h570, h591, h596, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h570, h596, hc12, hlam, hphi, ht23, ht34, u4elo4]
                            · linarith only [h3, h476, h593, hc02, hlam, hphi, ht23, ht34, u4elo0]
                      · linarith only [h476, h477, h566, h588, hc13, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h601 | h601
            · rcases m.htr 0 4 5 (by decide) (by decide) with h602 | h602
              · rcases m.htr 1 2 3 (by decide) (by decide) with h603 | h603
                · linarith only [h0, h338, h476, h601, h603, hc23, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h605 | h605
                  · linarith only [h0, h338, h476, h601, h605, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h607 | h607
                    · linarith only [h0, h338, h607, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h609 | h609
                      · linarith only [h1, h476, h601, h609, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h612 | h612
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                            · linarith only [h0, h3, h476, h613, hc12, hlam, hphi, u2elo2]
                            · linarith only [h0, h3, h613, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h476, h602, h612, hc14, hlam, hphi, u4elo3]
                        · linarith only [h476, h601, h611, hc13, hlam, hphi, ht34, u4elo3]
              · linarith only [h476, h601, h602, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h619 | h619
              · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
                · linarith only [h0, h3, h620, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h622 | h622
                  · linarith only [h0, h3, h476, h622, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h624 | h624
                    · linarith only [h0, h338, h624, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h626 | h626
                      · linarith only [h1, h476, h626, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h628 | h628
                        · linarith only [h1, h601, h628, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h630 | h630
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h631 | h631
                            · linarith only [h0, h3, h476, h631, hc12, hlam, hphi, u2elo2]
                            · linarith only [h0, h3, h631, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h619, h630, hc14, hlam, hphi, u4elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
                · linarith only [h0, h3, h635, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h637 | h637
                  · linarith only [h0, h3, h476, h637, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h639 | h639
                    · linarith only [h0, h338, h639, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h641 | h641
                      · linarith only [h1, h476, h641, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h643 | h643
                        · linarith only [h1, h601, h643, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h645 | h645
                          · linarith only [h3, h476, h619, h645, hc02, hlam, hphi, ht23, ht34, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h647 | h647
                            · linarith only [h0, h3, h476, h647, hc12, hlam, hphi, u2elo2]
                            · linarith only [h0, h3, h647, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h650 | h650
      · rcases m.htr 0 2 5 (by decide) (by decide) with h651 | h651
        · linarith only [h0, h2, h651, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h653 | h653
          · rcases m.htr 0 3 5 (by decide) (by decide) with h654 | h654
            · linarith only [h1, h2, h654, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h656 | h656
              · linarith only [h0, h2, h650, h653, h656, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h658 | h658
                · linarith only [h0, h2, h656, h658, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h650, h651, h658, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h661 | h661
            · linarith only [h0, h2, h653, h661, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h663 | h663
              · rcases m.htr 1 2 3 (by decide) (by decide) with h664 | h664
                · linarith only [h0, h2, h663, h664, hc23, hlam, hphi, ht34, u4elo0]
                · linarith only [h650, h651, h664, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
                · linarith only [h0, h2, h663, h667, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h650, h651, h667, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h670 | h670
        · linarith only [h0, h2, h650, h670, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h672 | h672
          · rcases m.htr 0 3 5 (by decide) (by decide) with h673 | h673
            · linarith only [h1, h2, h673, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h675 | h675
              · linarith only [h1, h2, h672, h675, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h677 | h677
                · linarith only [h650, h677, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
                  · linarith only [h1, h2, h675, h677, h679, hc24, hlam, hphi, u4elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h681 | h681
                    · linarith only [h1, h2, h670, h675, h677, h681, hc02, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h1, h2, h677, h681, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h684 | h684
            · linarith only [h0, h2, h672, h684, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h686 | h686
              · rcases m.htr 1 2 3 (by decide) (by decide) with h687 | h687
                · linarith only [h0, h2, h686, h687, hc23, hlam, hphi, ht34, u4elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h689 | h689
                  · linarith only [h1, h2, h672, h686, h687, h689, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h691 | h691
                    · linarith only [h1, h2, h670, h672, h686, h687, h691, hc02, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h0, h2, h691, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h694 | h694
                · linarith only [h0, h650, h694, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h696 | h696
                  · linarith only [h0, h650, h672, h696, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h698 | h698
                    · linarith only [h0, h670, h698, hlam]
                    · linarith only [h1, h2, h694, h698, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h701 | h701
    · rcases m.htr 0 2 3 (by decide) (by decide) with h702 | h702
      · linarith only [h0, h1, h702, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h704 | h704
        · rcases m.htr 0 3 4 (by decide) (by decide) with h705 | h705
          · rcases m.htr 0 3 5 (by decide) (by decide) with h706 | h706
            · rcases m.htr 0 4 5 (by decide) (by decide) with h707 | h707
              · rcases m.htr 1 2 3 (by decide) (by decide) with h708 | h708
                · linarith only [h0, h1, h702, h708, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h708, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h711 | h711
                · linarith only [h0, h1, h702, h711, hlam]
                · linarith only [h0, h1, h711, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h704, h706, hlam]
          · linarith only [h0, h1, h705, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h716 | h716
          · rcases m.htr 0 3 5 (by decide) (by decide) with h717 | h717
            · rcases m.htr 0 4 5 (by decide) (by decide) with h718 | h718
              · rcases m.htr 1 2 3 (by decide) (by decide) with h719 | h719
                · linarith only [h0, h1, h702, h719, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h719, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h722 | h722
                · linarith only [h0, h1, h702, h717, h722, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h0, h1, h722, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h701, h717, hlam]
          · linarith only [h0, h1, h716, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h727 | h727
      · linarith only [h0, h1, h727, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h729 | h729
        · linarith only [h0, h701, h729, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h731 | h731
          · rcases m.htr 0 3 5 (by decide) (by decide) with h732 | h732
            · rcases m.htr 0 4 5 (by decide) (by decide) with h733 | h733
              · rcases m.htr 1 2 3 (by decide) (by decide) with h734 | h734
                · linarith only [h0, h1, h727, h734, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h734, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h737 | h737
                · linarith only [h0, h727, h737, hlam]
                · linarith only [h0, h1, h737, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h740 | h740
              · linarith only [h731, h732, h740, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h742 | h742
                · linarith only [h0, h1, h732, h742, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1, h742, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1, h731, hc12, hlam, hphi, ht23, ht34, u4elo3]

end R2N4
