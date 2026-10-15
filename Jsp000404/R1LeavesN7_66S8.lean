import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_H_I_L_0_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h4elo := hb4.1
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
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
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
                                linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h12, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h14, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                rcases p15_3 (m.d 0 1) (by simp) with h20 | h20
                                · rcases p15_3 (m.d 0 2) (by simp) with h21 | h21
                                  · linarith only [h0, h21, hlam]
                                  · linarith only [h21, h5, hlam]
                                · linarith only [h20, hlam, p15_0]
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
                                linarith only [h1, h12, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h10, h14, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15_1, u2elo0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p15_1, u2elo0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h1, hlam, p15_1]
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
                                linarith only [h10, h14, h2, hc03, hc45, hlam, hphi, ht0b, ht5b, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h3, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p15_1, u2elo0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h2, hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h4, hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h6, hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p15_1, u4elo0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h0, h12, h9, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h5, hlam, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h7, hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h8, hlam, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hlam, p15_0]
                            · linarith only [h14, h8, hc24, hlam, hphi, u4elo0]
                          · linarith only [h12, h13, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                          · linarith only [h12, h3, h47, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
                            · rcases h0bigk with h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h12, h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h4, h49, hc01, hc45, hlam, hphi, ht0b, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h47, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h0, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h12, h6, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h47, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p50_1, u2elo0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h47, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p50_1, u2elo0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h1, hlam, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h3, hlam, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h47, h7, h8, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h3, h47, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p50_1, u2elo0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h2, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h4, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h6, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h47, h7, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h0, h10, h49, hc05, hc45, hlam, hphi, ht0b, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h5, hlam, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h7, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h8, hlam, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                            · linarith only [h49, h8, hc24, hlam, hphi, u4elo0]
                      · linarith only [h11, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h10, h9, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h3, h9, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                            · linarith only [h2, h8, h81, h85, hlam]
                            · rcases h0bigk with h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h0, h80, h83, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h1, h80, h83, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                rcases p87_3 (m.d 0 1) (by simp) with h91 | h91
                                · rcases p87_3 (m.d 0 2) (by simp) with h92 | h92
                                  · linarith only [h0, h92, hlam]
                                  · linarith only [h4, h92, hlam]
                                · linarith only [h2, h91, hlam]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                rcases p87_3 (m.d 0 1) (by simp) with h96 | h96
                                · rcases p87_3 (m.d 0 2) (by simp) with h97 | h97
                                  · linarith only [h0, h97, hlam]
                                  · linarith only [h5, h97, hlam]
                                · linarith only [h96, hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h0, hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h1, h80, h83, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p87_1, u2elo0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p87_1, u2elo0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h1, hlam, p87_1]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h3, hlam, p87_1]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h2, h3, h81, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p87_1, u2elo0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h3, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p87_1, u2elo0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h2, hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h4, hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h6, hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h8, hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h0, h80, h83, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h5, hlam, p87_1]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h7, hlam, p87_0]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [h2, h8, h81, h83, hc34, hlam, hphi, p87_1, u4elo4]
                              · have p87_0 := h87c.1
                                have p87_1 := h87c.2.1
                                have p87_2 := h87c.2.2.1
                                have p87_3 := h87c.2.2.2
                                linarith only [hlam, p87_0]
                          · linarith only [h3, h7, h83, h84, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · linarith only [h6, h8, h83, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h5, h82, hc12, hlam, hphi, u2elo0]
                    · linarith only [h80, h81, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h3, h80, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                · linarith only [h126, h6, h7, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                          · linarith only [h0, h128, h132, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                            · linarith only [h126, h129, h134, hc04, hlam, hphi, u4elo1]
                            · rcases h0bigk with h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h0, h130, h131, h132, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h1, h128, h131, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                rcases p136_3 (m.d 0 1) (by simp) with h140 | h140
                                · rcases p136_3 (m.d 0 2) (by simp) with h141 | h141
                                  · linarith only [h0, h141, hlam]
                                  · linarith only [h141, h4, hlam]
                                · linarith only [h140, h2, hlam]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h1, h128, h131, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h0, hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h1, h128, h131, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p136_1, u2elo0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h129, h131, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p136_1, u2elo0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h1, h128, h131, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p136_1, u2elo0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h1, hlam, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h3, hlam, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h129, h131, h2, h7, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h7, hlam, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h2, hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h4, hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h6, hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h126, hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h126, hc01, hlam, hphi, ht12, ht23, ht34, p136_1, u4elo4]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h5, hlam, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h126, hc03, hlam, hphi, ht34, p136_1, u4elo4]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h126, h129, h131, h2, hc34, hlam, hphi, p136_1, u4elo4]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hlam, p136_0]
                        · linarith only [h131, h6, h7, hc23, hc35, hlam, hphi]
                      · linarith only [h128, h130, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h128, h129, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h128, h3, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
              · rcases m.htr 0 4 5 (by decide) (by decide) with h171 | h171
                · rcases m.htr 1 2 3 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                        · linarith only [h170, h175, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                            · rcases h0bigk with h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [hlam, p179_0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h0, h173, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p179_1]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h1, h172, h177, hc01, hc35, hlam, hphi, ht0b, ht5b, p179_1]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h178, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p179_1]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                rcases p179_3 (m.d 0 1) (by simp) with h184 | h184
                                · rcases p179_3 (m.d 0 2) (by simp) with h185 | h185
                                  · linarith only [h0, h185, hlam]
                                  · linarith only [h185, h5, hlam]
                                · linarith only [h184, hlam, p179_0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h0, hlam, p179_0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [hlam, p179_0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h1, h172, h177, hc02, hc35, hlam, hphi, ht0b, ht5b, p179_1]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h1, h172, h177, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p179_1, u2elo0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p179_1, u2elo0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h1, hlam, p179_1]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h3, hlam, p179_1]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [hlam, p179_0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h6, hlam, p179_1]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p179_1, u4elo0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h2, hlam, p179_0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h4, hlam, p179_0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [hc03, hlam, hphi, ht34, p179_1, u4elo0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [hlam, p179_0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p179_1, u4elo3]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h0, h173, h175, h177, hc05, hc35, hlam, hphi, ht0b, ht5b, p179_1]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h5, hlam, p179_1]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h170, hlam, p179_0]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [h171, hlam, p179_1]
                              · have p179_0 := h179c.1
                                have p179_1 := h179c.2.1
                                have p179_2 := h179c.2.2.1
                                have p179_3 := h179c.2.2.2
                                linarith only [hlam, p179_0]
                            · linarith only [h171, h175, h177, h178, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h170, h177, h6, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h172, h174, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h172, h173, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h172, h3, hc12, hlam, hphi, u2elo0]
                · linarith only [h170, h171, h6, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
                · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h217 | h217
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h218 | h218
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                        · linarith only [h215, h216, h219, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h221 | h221
                          · linarith only [h170, h217, h219, h221, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h223 | h223
                            · rcases h0bigk with h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [hlam, p224_0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h0, h217, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p224_1]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                rcases p224_3 (m.d 0 1) (by simp) with h227 | h227
                                · rcases p224_3 (m.d 0 2) (by simp) with h228 | h228
                                  · linarith only [h0, h228, hlam]
                                  · linarith only [h228, h3, hlam]
                                · linarith only [h1, h227, hlam]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h223, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p224_1]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                rcases p224_3 (m.d 0 1) (by simp) with h233 | h233
                                · rcases p224_3 (m.d 0 2) (by simp) with h234 | h234
                                  · linarith only [h0, h234, hlam]
                                  · linarith only [h234, h5, hlam]
                                · linarith only [h233, hlam, p224_0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h0, hlam, p224_0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [hlam, p224_0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h1, h216, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p224_1, u2elo0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h2, h217, h223, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p224_1, u2elo0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p224_1, u2elo0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h1, hlam, p224_1]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h3, hlam, p224_1]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [hlam, p224_0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h6, hlam, p224_1]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h170, hlam, p224_1]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h2, hlam, p224_0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h4, hlam, p224_0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h1, h216, hc23, hlam, hphi, ht34, p224_1, u4elo0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [hlam, p224_0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h1, h170, h216, h6, hc23, hlam, hphi, ht34, p224_1, u4elo3]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h0, h217, h223, hc05, hc45, hlam, hphi, ht0b, ht5b, p224_1]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h5, hlam, p224_1]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h1, h216, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p224_1, u2elo0]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [h215, hlam, p224_1]
                              · have p224_0 := h224c.1
                                have p224_1 := h224c.2.1
                                have p224_2 := h224c.2.2.1
                                have p224_3 := h224c.2.2.2
                                linarith only [hlam, p224_0]
                            · linarith only [h215, h223, h6, hc24, hlam, hphi, u4elo3]
                      · linarith only [h218, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h216, h217, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h216, h3, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h264 | h264
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h265 | h265
                        · linarith only [h215, h265, h3, h6, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h267 | h267
                          · linarith only [h1, h170, h263, h265, h267, hc13, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h269 | h269
                            · linarith only [h2, h215, h263, h269, hlam]
                            · rcases h0bigk with h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h0, h264, hc01, hc25, hlam, hphi, ht0b, ht5b, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                rcases p271_3 (m.d 0 1) (by simp) with h274 | h274
                                · rcases p271_3 (m.d 0 2) (by simp) with h275 | h275
                                  · linarith only [h0, h275, hlam]
                                  · linarith only [h275, h3, hlam]
                                · linarith only [h1, h274, hlam]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                rcases p271_3 (m.d 0 1) (by simp) with h279 | h279
                                · rcases p271_3 (m.d 0 2) (by simp) with h280 | h280
                                  · linarith only [h0, h280, hlam]
                                  · linarith only [h280, h4, hlam]
                                · linarith only [h2, h279, hlam]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                rcases p271_3 (m.d 0 1) (by simp) with h284 | h284
                                · rcases p271_3 (m.d 0 2) (by simp) with h285 | h285
                                  · linarith only [h0, h285, hlam]
                                  · linarith only [h285, h5, hlam]
                                · linarith only [h284, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h0, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h1, h262, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p271_1, u2elo0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p271_1, u2elo0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p271_1, u2elo0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h1, hlam, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h3, hlam, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h6, hlam, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h170, hlam, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h2, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h4, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h1, h262, hc23, hlam, hphi, ht34, p271_1, u4elo0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h215, hlam, p271_0]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h0, h264, h265, h269, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h5, hlam, p271_1]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h1, h215, h262, hc23, hlam, hphi, ht34, p271_1, u4elo4]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [h215, hc04, hlam, hphi, p271_1, u4elo4]
                              · have p271_0 := h271c.1
                                have p271_1 := h271c.2.1
                                have p271_2 := h271c.2.2.1
                                have p271_3 := h271c.2.2.2
                                linarith only [hlam, p271_0]
                      · linarith only [h264, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h262, h263, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h262, h3, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h312 | h312
            · rcases m.htr 0 3 5 (by decide) (by decide) with h313 | h313
              · linarith only [h3, h313, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h315 | h315
                · linarith only [h315, h4, h5, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h319 | h319
                      · linarith only [h0, h319, h5, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
                        · linarith only [h0, h317, h321, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h3, h312, h321, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h318, h4, h5, hc12, hlam, hphi, u2elo4]
                  · linarith only [h3, h317, h5, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h326 | h326
              · linarith only [h3, h326, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h328 | h328
                · linarith only [h328, h4, h5, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h332 | h332
                      · linarith only [h332, h5, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
                        · linarith only [h0, h330, h334, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                          · linarith only [h0, h326, h331, h334, h336, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h338 | h338
                            · linarith only [h0, h328, h331, h338, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                            · linarith only [h0, h331, h338, h5, hc24, hlam, hphi, u4elo4]
                    · linarith only [h330, h331, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h3, h330, h5, hc12, hlam, hphi, u2elo4]
        · linarith only [h3, h4, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h344 | h344
        · rcases m.htr 0 2 5 (by decide) (by decide) with h345 | h345
          · rcases m.htr 0 3 4 (by decide) (by decide) with h346 | h346
            · rcases m.htr 0 3 5 (by decide) (by decide) with h347 | h347
              · rcases m.htr 0 4 5 (by decide) (by decide) with h348 | h348
                · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
                  · linarith only [h0, h3, h344, h349, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h351 | h351
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h352 | h352
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h354 | h354
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                            · linarith only [h0, h3, h351, h355, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                            · linarith only [h3, h344, h348, h353, h355, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · linarith only [h0, h3, h347, h352, h354, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h1, h3, h349, h351, h353, hc24, hlam, hphi, u4elo3]
                      · linarith only [h3, h345, h351, h352, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · linarith only [h3, h344, h351, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
                  · linarith only [h3, h362, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h364 | h364
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h365 | h365
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h366 | h366
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h367 | h367
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h368 | h368
                            · linarith only [h0, h3, h348, h364, h368, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases h0bigk with h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h0, h365, h368, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p370_1]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h0, h3, h365, h366, h368, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p370_1]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                rcases p370_3 (m.d 0 1) (by simp) with h374 | h374
                                · rcases p370_3 (m.d 0 2) (by simp) with h375 | h375
                                  · linarith only [h0, h375, hlam]
                                  · linarith only [h344, h375, hlam]
                                · linarith only [h2, h374, hlam]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                rcases p370_3 (m.d 0 1) (by simp) with h379 | h379
                                · rcases p370_3 (m.d 0 2) (by simp) with h380 | h380
                                  · linarith only [h0, h380, hlam]
                                  · linarith only [h345, h380, hlam]
                                · linarith only [h379, hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h0, hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h3, hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h2, h3, h364, h366, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p370_1, u2elo2]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h3, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p370_1, u2elo2]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h1, hlam, p370_1]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h0, h365, hc03, hc25, hlam, hphi, ht0b, ht5b, p370_1]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h2, h3, h364, h366, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p370_1, u2elo2]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h3, h345, h367, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p370_1, u2elo2]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h2, hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h344, hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h346, hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h348, hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h0, h365, h366, h368, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p370_1]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h345, hlam, p370_1]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h347, hlam, p370_0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [h2, h345, h364, h366, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p370_1, u2elo0]
                              · have p370_0 := h370c.1
                                have p370_1 := h370c.2.1
                                have p370_2 := h370c.2.2.1
                                have p370_3 := h370c.2.2.2
                                linarith only [hlam, p370_0]
                          · linarith only [h3, h347, h367, hlam]
                        · linarith only [h3, h366, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h3, h345, h365, hc12, hlam, hphi, u2elo2]
                    · linarith only [h3, h344, h364, hc12, hlam, hphi, u2elo2]
              · linarith only [h3, h345, h347, hlam]
            · linarith only [h3, h344, h346, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h410 | h410
            · rcases m.htr 0 3 5 (by decide) (by decide) with h411 | h411
              · rcases m.htr 0 4 5 (by decide) (by decide) with h412 | h412
                · linarith only [h344, h345, h412, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h414 | h414
                  · linarith only [h0, h3, h344, h414, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h416 | h416
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h417 | h417
                      · linarith only [h0, h345, h417, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
                            · linarith only [h0, h345, h412, h416, h420, h421, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · linarith only [h0, h345, h416, h421, hc24, hlam, hphi, u4elo4]
                          · linarith only [h0, h3, h411, h416, h420, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h3, h416, h419, hc24, hlam, hphi, u4elo3]
                    · linarith only [h3, h344, h416, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
                · linarith only [h3, h344, h411, h427, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h429 | h429
                  · linarith only [h3, h429, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h431 | h431
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h432 | h432
                      · linarith only [h0, h345, h432, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h434 | h434
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h435 | h435
                          · linarith only [h0, h3, h411, h431, h434, h435, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h437 | h437
                            · linarith only [h0, h427, h431, h437, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · linarith only [h3, h344, h434, h435, h437, hc34, hlam, hphi, u4elo4]
                        · linarith only [h0, h3, h431, h434, hc24, hlam, hphi, u4elo3]
                    · linarith only [h3, h344, h431, hc12, hlam, hphi, u2elo2]
            · linarith only [h3, h344, h410, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h443 | h443
          · rcases m.htr 0 3 4 (by decide) (by decide) with h444 | h444
            · rcases m.htr 0 3 5 (by decide) (by decide) with h445 | h445
              · rcases m.htr 0 4 5 (by decide) (by decide) with h446 | h446
                · rcases m.htr 1 2 3 (by decide) (by decide) with h447 | h447
                  · linarith only [h0, h344, h447, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h449 | h449
                    · linarith only [h0, h344, h449, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h451 | h451
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h452 | h452
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h453 | h453
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h454 | h454
                            · rcases h0bigk with h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [hlam, p455_0]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h0, h451, hc01, hc25, hlam, hphi, ht0b, ht5b, p455_1]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h0, h344, h444, h451, h453, hc01, hc35, hlam, hphi, ht0b, ht5b, p455_1]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h0, h344, h451, h453, hc01, hc35, hlam, hphi, ht0b, ht5b, p455_1]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                rcases p455_3 (m.d 0 1) (by simp) with h460 | h460
                                · rcases p455_3 (m.d 0 2) (by simp) with h461 | h461
                                  · linarith only [h0, h461, hlam]
                                  · linarith only [h443, h461, hlam]
                                · linarith only [h460, hlam, p455_0]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h0, hlam, p455_0]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [hlam, p455_0]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h3, hlam, p455_0]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h344, hlam, p455_1]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h344, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p455_1, u4elo2]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h1, hlam, p455_1]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h0, h451, hc03, hc25, hlam, hphi, ht0b, ht5b, p455_1]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [hlam, p455_0]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h0, h3, h344, h451, h453, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p455_1, u2elo2]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h3, h443, h453, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p455_1, u2elo2]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h2, hlam, p455_0]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h0, h451, h453, hc04, hc35, hlam, hphi, ht0b, ht5b, p455_1]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h444, hlam, p455_0]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [hlam, p455_0]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h344, h443, h453, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p455_1, u4elo2]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h0, h451, h453, hc05, hc35, hlam, hphi, ht0b, ht5b, p455_1]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h443, hlam, p455_1]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h445, hlam, p455_0]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [h446, hlam, p455_1]
                              · have p455_0 := h455c.1
                                have p455_1 := h455c.2.1
                                have p455_2 := h455c.2.2.1
                                have p455_3 := h455c.2.2.2
                                linarith only [hlam, p455_0]
                            · linarith only [h0, h344, h451, h453, h454, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                          · linarith only [h3, h445, h453, hlam]
                        · linarith only [h3, h444, h452, hlam]
                      · linarith only [h443, h451, hc12, hlam, hphi, u2elo0]
                · linarith only [h344, h443, h446, hlam]
              · linarith only [h3, h443, h445, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h491 | h491
              · rcases m.htr 0 4 5 (by decide) (by decide) with h492 | h492
                · rcases m.htr 1 2 3 (by decide) (by decide) with h493 | h493
                  · linarith only [h0, h3, h443, h493, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h495 | h495
                    · linarith only [h0, h344, h495, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h497 | h497
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h498 | h498
                        · linarith only [h3, h444, h498, hc02, hlam, hphi, u2elo2]
                        · linarith only [h0, h3, h497, h498, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h344, h443, h497, hc12, hlam, hphi, ht23, ht34, u4elo2]
                · linarith only [h3, h443, h444, h492, hlam]
              · linarith only [h3, h443, h491, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h504 | h504
            · rcases m.htr 0 3 5 (by decide) (by decide) with h505 | h505
              · rcases m.htr 0 4 5 (by decide) (by decide) with h506 | h506
                · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
                  · linarith only [h0, h3, h507, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h509 | h509
                    · linarith only [h0, h344, h509, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h511 | h511
                      · linarith only [h0, h443, h511, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h513 | h513
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h514 | h514
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h515 | h515
                            · rcases h0bigk with h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                rcases p516_3 (m.d 0 1) (by simp) with h518 | h518
                                · rcases p516_3 (m.d 0 2) (by simp) with h519 | h519
                                  · linarith only [h0, h519, hlam]
                                  · rcases p516_3 (m.d 0 3) (by simp) with h521 | h521
                                    · linarith only [h1, h521, hlam]
                                    · linarith only [h3, h521, hlam]
                                · linarith only [h0, h518, hlam]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h505, hc01, hc35, hlam, hphi, ht0b, ht5b, p516_1]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h506, hc01, hc45, hlam, hphi, ht0b, ht5b, p516_1]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                rcases p516_3 (m.d 0 1) (by simp) with h527 | h527
                                · rcases p516_3 (m.d 0 2) (by simp) with h528 | h528
                                  · linarith only [h0, h528, hlam]
                                  · rcases p516_3 (m.d 0 3) (by simp) with h530 | h530
                                    · linarith only [h1, h530, hlam]
                                    · linarith only [h505, h530, hlam]
                                · linarith only [h527, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h0, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h3, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h344, hlam, p516_1]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h443, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h1, hlam, p516_1]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h3, hc02, hlam, hphi, p516_1, u2elo2]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h3, h506, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p516_1, u2elo2]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h0, h3, h443, hc12, hlam, hphi, p516_1, u2elo2]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h2, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, ht34, p516_1, u4elo0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h504, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h0, h344, h443, hc12, hlam, hphi, ht23, ht34, p516_1, u4elo2]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p516_1]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h0, h443, hc12, hlam, hphi, p516_1, u2elo4]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h505, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h506, hlam, p516_1]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [hlam, p516_0]
                            · linarith only [h0, h344, h515, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h0, h3, h505, h506, h514, hc12, hlam, hphi, ht23, ht34, u4elo0]
                        · linarith only [h0, h3, h513, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h557 | h557
                  · linarith only [h0, h3, h557, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h559 | h559
                    · linarith only [h0, h344, h559, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h561 | h561
                      · linarith only [h0, h443, h561, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h563 | h563
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h564 | h564
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h565 | h565
                            · linarith only [h344, h506, h565, hc02, hlam, hphi, ht23, ht34, u4elo2]
                            · linarith only [h0, h344, h565, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h3, h505, h564, hlam]
                        · linarith only [h0, h3, h563, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h570 | h570
                · linarith only [h504, h505, h570, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h572 | h572
                  · linarith only [h0, h3, h572, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h574 | h574
                    · linarith only [h0, h344, h574, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h576 | h576
                      · linarith only [h0, h3, h443, h504, h505, h576, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h579 | h579
                          · linarith only [h504, h505, h579, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h581 | h581
                            · linarith only [h344, h570, h581, hc02, hlam, hphi, ht23, ht34, u4elo2]
                            · linarith only [h0, h344, h581, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h0, h3, h578, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h585 | h585
              · rcases m.htr 0 4 5 (by decide) (by decide) with h586 | h586
                · rcases m.htr 1 2 3 (by decide) (by decide) with h587 | h587
                  · linarith only [h0, h344, h587, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h589 | h589
                    · linarith only [h0, h344, h589, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h591 | h591
                      · linarith only [h0, h443, h591, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h593 | h593
                        · linarith only [h443, h504, h585, h593, hc02, hlam, hphi, u2elo2]
                        · linarith only [h0, h3, h593, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h504, h585, h586, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h597 | h597
                · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                  · linarith only [h0, h3, h598, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h600 | h600
                    · linarith only [h0, h344, h600, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h602 | h602
                      · linarith only [h0, h443, h602, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
                        · linarith only [h0, h3, h504, h604, hc12, hlam, hphi, u2elo2]
                        · linarith only [h0, h3, h604, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h607 | h607
                  · linarith only [h0, h3, h607, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h609 | h609
                    · linarith only [h0, h344, h609, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h611 | h611
                      · linarith only [h0, h443, h611, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                        · linarith only [h0, h3, h504, h613, hc12, hlam, hphi, u2elo2]
                        · linarith only [h0, h3, h613, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h617 | h617
    · rcases m.htr 0 2 3 (by decide) (by decide) with h618 | h618
      · linarith only [h0, h1, h618, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h620 | h620
        · rcases m.htr 0 2 5 (by decide) (by decide) with h621 | h621
          · rcases m.htr 0 3 4 (by decide) (by decide) with h622 | h622
            · rcases m.htr 0 3 5 (by decide) (by decide) with h623 | h623
              · rcases m.htr 0 4 5 (by decide) (by decide) with h624 | h624
                · rcases m.htr 1 2 3 (by decide) (by decide) with h625 | h625
                  · linarith only [h0, h1, h618, h625, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h625, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
                  · linarith only [h0, h1, h618, h628, hlam]
                  · linarith only [h0, h1, h628, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h1, h621, h623, hlam]
            · linarith only [h0, h1, h622, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h633 | h633
            · rcases m.htr 0 3 5 (by decide) (by decide) with h634 | h634
              · rcases m.htr 0 4 5 (by decide) (by decide) with h635 | h635
                · linarith only [h620, h621, h635, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
                  · linarith only [h0, h618, h637, hlam]
                  · linarith only [h0, h1, h637, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h640 | h640
                · linarith only [h1, h617, h634, h640, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h642 | h642
                  · linarith only [h0, h1, h634, h642, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h642, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h633, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h646 | h646
          · rcases m.htr 0 3 4 (by decide) (by decide) with h647 | h647
            · rcases m.htr 0 3 5 (by decide) (by decide) with h648 | h648
              · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
                · rcases m.htr 1 2 3 (by decide) (by decide) with h650 | h650
                  · linarith only [h0, h620, h650, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1, h650, hc12, hlam, hphi, u2elo2]
                · linarith only [h620, h646, h649, hlam]
              · linarith only [h0, h1, h620, h646, h648, hc12, hlam, hphi, u2elo3]
            · linarith only [h0, h1, h647, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h656 | h656
            · rcases m.htr 0 3 5 (by decide) (by decide) with h657 | h657
              · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
                · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                  · linarith only [h0, h620, h659, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1, h659, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
                  · linarith only [h0, h620, h658, h662, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h1, h662, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h665 | h665
                · linarith only [h1, h617, h657, h665, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
                  · linarith only [h0, h1, h657, h667, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h667, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h656, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · linarith only [h0, h617, hc12, hlam, hphi, ht23, ht34, u4elo1]

end R2N4
