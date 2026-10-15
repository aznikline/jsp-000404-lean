import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h10, h14, h16, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · linarith only [h0, h10, h14, h15, h16, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h15, h19, h4, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases h0bigk with h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h15, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h14, h15, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h0, hlam, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h14, h15, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21_1, u2elo0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h14, h15, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21_1, u2elo0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p21_1, u2elo0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h1, hlam, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h4, hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h14, h15, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p21_1, u2elo0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h2, hlam, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h5, hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h7, hlam, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h3, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p21_1, u2elo0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h3, hlam, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h6, hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h8, hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h9, hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [hlam, p21_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                        · rcases h0bigk with h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h14, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h14, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h47, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            rcases p49_3 (m.d 0 1) (by simp) with h54 | h54
                            · rcases p49_3 (m.d 0 2) (by simp) with h55 | h55
                              · linarith only [h0, h55, hlam]
                              · linarith only [h55, h6, hlam]
                            · linarith only [h3, h54, hlam]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h0, hlam, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h14, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h14, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p49_1, u2elo0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h12, h3, h47, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p49_1, u2elo0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h1, hlam, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h4, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h14, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h12, h3, h4, h47, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p49_1, u2elo0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h2, hlam, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h5, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h7, hlam, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h12, h3, h47, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p49_1, u2elo0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h3, hlam, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h6, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h8, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h9, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [hlam, p49_0]
                        · linarith only [h14, h47, h48, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                        · linarith only [h4, h47, h7, h80, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · linarith only [h14, h4, h7, h80, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                    · linarith only [h10, h13, h4, h8, h83, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h86 | h86
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
                            linarith only [h13, h4, h7, h86, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h10, h13, h7, h86, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h5, h85, hc01, hc45, hlam, hphi, ht0b, ht5b, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h10, h13, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h0, hlam, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [hlam, p87_0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h10, h13, h7, h86, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p87_1, u2elo0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h10, h13, h7, h86, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p87_1, u2elo0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h10, h13, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p87_1, u2elo0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h1, hlam, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h4, hlam, p87_0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [hlam, p87_0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h10, h13, h7, h86, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h10, h13, h4, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p87_1, u2elo0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h2, hlam, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h5, hlam, p87_0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h7, hlam, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [hlam, p87_0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h10, h13, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h3, hlam, p87_1]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h6, hlam, p87_0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h8, hlam, p87_0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [h9, hlam, p87_0]
                          · have p87_0 := h87c.1
                            have p87_1 := h87c.2.1
                            have p87_2 := h87c.2.2.1
                            have p87_3 := h87c.2.2.2
                            linarith only [hlam, p87_0]
                        · linarith only [h5, h85, h86, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h114 | h114
                        · linarith only [h114, h4, h7, h85, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · linarith only [h114, h4, h7, h83, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h12, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h120 | h120
            · rcases m.htr 1 2 4 (by decide) (by decide) with h121 | h121
              · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                · rcases m.htr 1 3 5 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h125 | h125
                      · linarith only [h120, h124, h125, h9, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                        · linarith only [h121, h124, h127, h2, h9, hlam]
                        · rcases h0bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h0, h120, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            rcases p129_3 (m.d 0 1) (by simp) with h133 | h133
                            · rcases p129_3 (m.d 0 2) (by simp) with h134 | h134
                              · linarith only [h0, h134, hlam]
                              · linarith only [h134, h5, hlam]
                            · linarith only [h133, h2, hlam]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            rcases p129_3 (m.d 0 1) (by simp) with h138 | h138
                            · rcases p129_3 (m.d 0 2) (by simp) with h139 | h139
                              · linarith only [h0, h139, hlam]
                              · linarith only [h139, h6, hlam]
                            · linarith only [h138, h3, hlam]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h0, hlam, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h1, h123, h127, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h121, h124, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p129_1, u2elo0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h121, h124, h2, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p129_1, u2elo0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h1, hlam, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h4, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h121, h124, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p129_1, u2elo0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h121, h124, h2, h4, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p129_1, u2elo0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h2, hlam, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h5, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h7, hlam, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h9, hlam, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h3, hlam, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h6, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h8, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h121, h124, h2, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p129_1, u2elo0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [hlam, p129_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h163 | h163
                      · linarith only [h121, h124, h163, h7, h9, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h165 | h165
                        · linarith only [h165, h2, h4, h7, h9, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases h0bigk with h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [hlam, p167_0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h0, h122, hc01, hc25, hlam, hphi, ht0b, ht5b, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h124, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h124, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h124, h165, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h0, hlam, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [hlam, p167_0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h124, h165, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p167_1, u2elo0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h124, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p167_1, u2elo0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p167_1, u2elo0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h1, hlam, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h4, hlam, p167_0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [hlam, p167_0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h124, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p167_1, u2elo0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h2, hlam, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h5, hlam, p167_0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h7, hlam, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [hlam, p167_0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h9, hlam, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h3, hlam, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h6, hlam, p167_0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h8, hlam, p167_0]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [h124, h7, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p167_1]
                          · have p167_0 := h167c.1
                            have p167_1 := h167c.2.1
                            have p167_2 := h167c.2.2.1
                            have p167_3 := h167c.2.2.2
                            linarith only [hlam, p167_0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                    · linarith only [h120, h123, h193, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                      · linarith only [h121, h195, h2, h9, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h197 | h197
                        · linarith only [h197, h7, h9, hlam]
                        · rcases h0bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h0, h122, h195, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h193, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h193, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h193, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h0, hlam, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h193, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h193, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p199_1, u2elo0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h193, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p199_1, u2elo0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h1, hlam, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h4, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h193, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h193, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p199_1, u2elo0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h2, hlam, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h5, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h7, hlam, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h9, hlam, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h3, hlam, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h6, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h8, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h193, h7, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [hlam, p199_0]
                · linarith only [h122, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h120, h121, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h120, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h228 | h228
          · linarith only [h228, h7, h8, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
            · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
              · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
                · rcases m.htr 1 3 5 (by decide) (by decide) with h233 | h233
                  · linarith only [h1, h233, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h236 | h236
                      · linarith only [h2, h228, h231, h236, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                        · linarith only [h228, h230, h235, h238, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [hlam, p240_0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h0, h230, h235, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h235, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            rcases p240_3 (m.d 0 1) (by simp) with h244 | h244
                            · rcases p240_3 (m.d 0 2) (by simp) with h245 | h245
                              · linarith only [h0, h245, hlam]
                              · linarith only [h245, h5, hlam]
                            · linarith only [h2, h244, hlam]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h1, h230, h235, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h0, hlam, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [hlam, p240_0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h1, h230, h235, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h2, h231, h235, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p240_1, u2elo0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h1, h230, h235, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p240_1, u2elo0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h1, hlam, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h4, hlam, p240_0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [hlam, p240_0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h2, h231, h235, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p240_1, u2elo0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h8, hlam, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h2, hlam, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h5, hlam, p240_0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h7, hlam, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [hlam, p240_0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h228, hlam, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h3, hlam, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h6, hlam, p240_0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h1, h230, h235, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p240_1]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [h2, h231, h235, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p240_1, u2elo0]
                          · have p240_0 := h240c.1
                            have p240_1 := h240c.2.1
                            have p240_2 := h240c.2.2.1
                            have p240_3 := h240c.2.2.2
                            linarith only [hlam, p240_0]
                    · linarith only [h235, h7, h8, hc23, hc35, hlam, hphi]
                · linarith only [h230, h232, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h230, h231, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h230, h4, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h274 | h274
        · rcases m.htr 0 4 5 (by decide) (by decide) with h275 | h275
          · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
            · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
              · rcases m.htr 1 2 5 (by decide) (by decide) with h278 | h278
                · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
                    · linarith only [h276, h280, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h282 | h282
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h283 | h283
                        · rcases h0bigk with h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [hlam, p284_0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p284_1]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h1, h279, h283, hc01, hc45, hlam, hphi, ht0b, ht5b, p284_1]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h1, h279, h283, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p284_1]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            rcases p284_3 (m.d 0 1) (by simp) with h289 | h289
                            · rcases p284_3 (m.d 0 2) (by simp) with h290 | h290
                              · linarith only [h0, h290, hlam]
                              · linarith only [h290, h6, hlam]
                            · linarith only [h289, h3, hlam]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h0, hlam, p284_1]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [hlam, p284_0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h1, h279, h283, hc02, hc45, hlam, hphi, ht0b, ht5b, p284_1]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h1, h279, h283, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p284_1, u2elo0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p284_1, u2elo0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h1, hlam, p284_1]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h4, hlam, p284_0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [hlam, p284_0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h7, hlam, p284_0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h278, h3, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p284_1]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h2, hlam, p284_1]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h5, hlam, p284_0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h1, h279, h283, hc04, hc45, hlam, hphi, ht0b, ht5b, p284_1]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [hlam, p284_0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h278, h3, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p284_1, u2elo0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h3, hlam, p284_1]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h6, hlam, p284_0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h274, hlam, p284_0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [h275, hlam, p284_0]
                          · have p284_0 := h284c.1
                            have p284_1 := h284c.2.1
                            have p284_2 := h284c.2.2.1
                            have p284_3 := h284c.2.2.2
                            linarith only [hlam, p284_0]
                        · linarith only [h277, h282, h283, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h315 | h315
                        · linarith only [h1, h279, h280, h282, h315, h7, hc23, hc34, hlam, hphi]
                        · linarith only [h275, h315, h5, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h274, h276, h279, h7, hc23, hc34, hlam, hphi]
                · linarith only [h278, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h276, h277, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h276, h4, hc12, hlam, hphi, u2elo0]
          · linarith only [h274, h275, h7, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h323 | h323
          · rcases m.htr 1 2 3 (by decide) (by decide) with h324 | h324
            · rcases m.htr 1 2 4 (by decide) (by decide) with h325 | h325
              · rcases m.htr 1 2 5 (by decide) (by decide) with h326 | h326
                · rcases m.htr 1 3 5 (by decide) (by decide) with h327 | h327
                  · linarith only [h1, h274, h327, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h329 | h329
                    · linarith only [h329, h4, h7, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h331 | h331
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                        · rcases h0bigk with h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [hlam, p333_0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h0, h325, h329, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p333_1]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            rcases p333_3 (m.d 0 1) (by simp) with h336 | h336
                            · rcases p333_3 (m.d 0 2) (by simp) with h337 | h337
                              · linarith only [h0, h337, hlam]
                              · linarith only [h337, h4, hlam]
                            · linarith only [h1, h336, hlam]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h2, h325, h331, hc01, hc45, hlam, hphi, ht0b, ht5b, p333_1]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            rcases p333_3 (m.d 0 1) (by simp) with h342 | h342
                            · rcases p333_3 (m.d 0 2) (by simp) with h343 | h343
                              · linarith only [h0, h343, hlam]
                              · linarith only [h343, h6, hlam]
                            · linarith only [h3, h342, hlam]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h0, hlam, p333_1]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [hlam, p333_0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h1, h324, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p333_1, u2elo0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h2, h325, h331, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p333_1, u2elo0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p333_1, u2elo0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h1, hlam, p333_1]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h4, hlam, p333_0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [hlam, p333_0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h7, hlam, p333_0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h274, hlam, p333_1]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h2, hlam, p333_1]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h5, hlam, p333_0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h1, h324, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p333_1, u2elo0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [hlam, p333_0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h3, h324, h327, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p333_1, u2elo0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h3, hlam, p333_1]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h6, hlam, p333_0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h1, h324, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p333_1, u2elo0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [h323, hlam, p333_0]
                          · have p333_0 := h333c.1
                            have p333_1 := h333c.2.1
                            have p333_2 := h333c.2.2.1
                            have p333_3 := h333c.2.2.2
                            linarith only [hlam, p333_0]
                        · linarith only [h2, h325, h331, h332, h7, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h368 | h368
                        · rcases h0bigk with h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h323, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            rcases p369_3 (m.d 0 1) (by simp) with h372 | h372
                            · rcases p369_3 (m.d 0 2) (by simp) with h373 | h373
                              · linarith only [h0, h373, hlam]
                              · linarith only [h373, h4, hlam]
                            · linarith only [h1, h372, hlam]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h323, h329, h331, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h323, h329, h331, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p369_1]
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
                            linarith only [h1, h324, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p369_1, u2elo0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h323, h329, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p369_1, u2elo0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h323, h329, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p369_1, u2elo0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h1, hlam, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h4, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h7, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h274, hlam, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h2, hlam, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h5, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h1, h324, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p369_1, u2elo0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h323, h329, h331, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p369_1, u2elo0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h3, hlam, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h6, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h1, h274, h324, hc23, hc35, hlam, hphi, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h323, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [hlam, p369_0]
                        · linarith only [h323, h368, h7, hlam]
                · linarith only [h326, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h324, h325, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h324, h4, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
            · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
              · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
                · rcases m.htr 1 3 5 (by decide) (by decide) with h406 | h406
                  · linarith only [h1, h274, h406, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
                    · linarith only [h4, h408, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h410 | h410
                      · linarith only [h323, h404, h410, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h412 | h412
                        · rcases h0bigk with h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [hlam, p413_0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p413_1]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            rcases p413_3 (m.d 0 1) (by simp) with h416 | h416
                            · rcases p413_3 (m.d 0 2) (by simp) with h417 | h417
                              · linarith only [h0, h417, hlam]
                              · linarith only [h4, h417, hlam]
                            · linarith only [h1, h416, hlam]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            rcases p413_3 (m.d 0 1) (by simp) with h421 | h421
                            · rcases p413_3 (m.d 0 2) (by simp) with h422 | h422
                              · linarith only [h0, h422, hlam]
                              · linarith only [h422, h5, hlam]
                            · linarith only [h2, h421, hlam]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            rcases p413_3 (m.d 0 1) (by simp) with h426 | h426
                            · rcases p413_3 (m.d 0 2) (by simp) with h427 | h427
                              · linarith only [h0, h427, hlam]
                              · linarith only [h427, h6, hlam]
                            · linarith only [h3, h426, hlam]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h0, hlam, p413_1]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [hlam, p413_0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h1, h403, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p413_1, u2elo0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h1, h403, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p413_1, u2elo0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p413_1, u2elo0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h1, hlam, p413_1]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h4, hlam, p413_0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [hlam, p413_0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h7, hlam, p413_0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h274, hlam, p413_1]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h2, hlam, p413_1]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h5, hlam, p413_0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h1, h403, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p413_1, u2elo0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [hlam, p413_0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h323, hlam, p413_1]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h3, hlam, p413_1]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h6, hlam, p413_0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h1, h403, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p413_1, u2elo0]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [h323, h412, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p413_1]
                          · have p413_0 := h413c.1
                            have p413_1 := h413c.2.1
                            have p413_2 := h413c.2.2.1
                            have p413_3 := h413c.2.2.2
                            linarith only [hlam, p413_0]
                        · rcases h0bigk with h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [hlam, p451_0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h0, h405, hc01, hc25, hlam, hphi, ht0b, ht5b, p451_1]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            rcases p451_3 (m.d 0 1) (by simp) with h454 | h454
                            · rcases p451_3 (m.d 0 2) (by simp) with h455 | h455
                              · linarith only [h0, h455, hlam]
                              · linarith only [h4, h455, hlam]
                            · linarith only [h1, h454, hlam]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            rcases p451_3 (m.d 0 1) (by simp) with h459 | h459
                            · rcases p451_3 (m.d 0 2) (by simp) with h460 | h460
                              · linarith only [h0, h460, hlam]
                              · linarith only [h460, h5, hlam]
                            · linarith only [h2, h459, hlam]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            rcases p451_3 (m.d 0 1) (by simp) with h464 | h464
                            · rcases p451_3 (m.d 0 2) (by simp) with h465 | h465
                              · linarith only [h0, h465, hlam]
                              · linarith only [h465, h6, hlam]
                            · linarith only [h3, h464, hlam]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h0, hlam, p451_1]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [hlam, p451_0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p451_1, u2elo0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p451_1, u2elo0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p451_1, u2elo0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h1, hlam, p451_1]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h4, hlam, p451_0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [hlam, p451_0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h7, hlam, p451_0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h274, hlam, p451_1]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h2, hlam, p451_1]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h5, hlam, p451_0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p451_1, u2elo0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [hlam, p451_0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h323, hlam, p451_1]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h3, hlam, p451_1]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h6, hlam, p451_0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h1, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p451_1, u2elo0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p451_1, u2elo0]
                          · have p451_0 := h451c.1
                            have p451_1 := h451c.2.1
                            have p451_2 := h451c.2.2.1
                            have p451_3 := h451c.2.2.2
                            linarith only [hlam, p451_0]
                · linarith only [h405, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h403, h404, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h4, h403, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h492 | h492
      · rcases m.htr 0 3 5 (by decide) (by decide) with h493 | h493
        · linarith only [h4, h493, h6, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h495 | h495
          · linarith only [h495, h5, h6, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
            · rcases m.htr 1 2 4 (by decide) (by decide) with h498 | h498
              · rcases m.htr 1 2 5 (by decide) (by decide) with h499 | h499
                · linarith only [h0, h499, h6, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h501 | h501
                  · linarith only [h1, h493, h501, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h503 | h503
                    · linarith only [h0, h497, h503, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h4, h492, h503, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h498, h5, h6, hc12, hlam, hphi, u2elo4]
            · linarith only [h4, h497, h6, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h508 | h508
        · linarith only [h492, h5, h508, h6, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h510 | h510
          · linarith only [h5, h510, h6, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
            · rcases m.htr 1 2 4 (by decide) (by decide) with h513 | h513
              · rcases m.htr 1 2 5 (by decide) (by decide) with h514 | h514
                · linarith only [h514, h6, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h516 | h516
                  · linarith only [h1, h508, h516, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h518 | h518
                    · linarith only [h0, h1, h492, h512, h518, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h520 | h520
                      · linarith only [h2, h510, h513, h520, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h522 | h522
                        · linarith only [h4, h520, h522, h6, hc23, hc34, hlam, hphi]
                        · rcases h0bigk with h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [hlam, p524_0]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h0, h513, h518, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p524_1]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            rcases p524_3 (m.d 0 1) (by simp) with h527 | h527
                            · rcases p524_3 (m.d 0 2) (by simp) with h528 | h528
                              · linarith only [h0, h528, hlam]
                              · linarith only [h4, h528, hlam]
                            · linarith only [h1, h527, hlam]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            rcases p524_3 (m.d 0 1) (by simp) with h532 | h532
                            · rcases p524_3 (m.d 0 2) (by simp) with h533 | h533
                              · linarith only [h0, h533, hlam]
                              · linarith only [h5, h533, hlam]
                            · linarith only [h2, h532, hlam]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h0, h513, h518, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p524_1]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h0, hlam, p524_1]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [hlam, p524_0]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h1, h512, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p524_1, u2elo4]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h1, h492, h512, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p524_1, u2elo4]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h6, hlam, p524_1]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h1, hlam, p524_1]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h4, hlam, p524_0]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [hlam, p524_0]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h492, hlam, p524_0]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h508, hlam, p524_1]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h2, hlam, p524_1]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h5, hlam, p524_0]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h1, h5, h512, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p524_1, u2elo4]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [hlam, p524_0]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h510, hlam, p524_1]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h3, hlam, p524_1]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p524_1]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h1, h512, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p524_1, u2elo4]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p524_1, u2elo4]
                          · have p524_0 := h524c.1
                            have p524_1 := h524c.2.1
                            have p524_2 := h524c.2.2.1
                            have p524_3 := h524c.2.2.2
                            linarith only [hlam, p524_0]
              · linarith only [h5, h513, hc12, hlam, hphi, u2elo0]
            · linarith only [h4, h512, h6, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h560 | h560
    · rcases m.htr 0 3 4 (by decide) (by decide) with h561 | h561
      · linarith only [h4, h5, h561, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h563 | h563
        · rcases m.htr 0 4 5 (by decide) (by decide) with h564 | h564
          · rcases m.htr 1 2 3 (by decide) (by decide) with h565 | h565
            · rcases m.htr 1 2 4 (by decide) (by decide) with h566 | h566
              · linarith only [h0, h5, h566, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h568 | h568
                · rcases m.htr 1 3 5 (by decide) (by decide) with h569 | h569
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h570 | h570
                    · linarith only [h0, h1, h5, h561, h565, h570, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h572 | h572
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h573 | h573
                        · rcases h0bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [hlam, p574_0]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h0, h565, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p574_1]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h1, h569, h573, hc01, hc45, hlam, hphi, ht0b, ht5b, p574_1]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h0, h5, h565, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p574_1]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            rcases p574_3 (m.d 0 1) (by simp) with h579 | h579
                            · rcases p574_3 (m.d 0 2) (by simp) with h580 | h580
                              · linarith only [h0, h580, hlam]
                              · linarith only [h560, h580, hlam]
                            · linarith only [h3, h579, hlam]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h0, hlam, p574_1]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [hlam, p574_0]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h1, h5, h569, h573, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p574_1, u2elo3]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h5, hlam, p574_1]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h5, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p574_1, u2elo3]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h1, hlam, p574_1]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h4, hlam, p574_0]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [hlam, p574_0]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h561, hlam, p574_0]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h3, h4, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p574_1, u2elo3]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h2, hlam, p574_1]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h0, h565, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p574_1]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p574_1, u2elo3]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [hlam, p574_0]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h5, h563, h573, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p574_1, u2elo3]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h3, hlam, p574_1]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h560, hlam, p574_0]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h563, hlam, p574_0]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [h564, hlam, p574_0]
                          · have p574_0 := h574c.1
                            have p574_1 := h574c.2.1
                            have p574_2 := h574c.2.2.1
                            have p574_3 := h574c.2.2.2
                            linarith only [hlam, p574_0]
                        · linarith only [h4, h5, h570, h572, h573, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h5, h565, h572, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h4, h5, h563, h569, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h5, h560, h565, h568, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h4, h5, h565, hc12, hlam, hphi, u2elo3]
          · linarith only [h4, h5, h563, h564, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h610 | h610
          · rcases m.htr 1 2 3 (by decide) (by decide) with h611 | h611
            · rcases m.htr 1 2 4 (by decide) (by decide) with h612 | h612
              · linarith only [h5, h612, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h614 | h614
                · rcases m.htr 1 3 5 (by decide) (by decide) with h615 | h615
                  · linarith only [h1, h563, h615, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h617 | h617
                    · linarith only [h4, h5, h617, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h619 | h619
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h620 | h620
                        · rcases h0bigk with h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [hlam, p621_0]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h0, h614, hc01, hc25, hlam, hphi, ht0b, ht5b, p621_1]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            rcases p621_3 (m.d 0 1) (by simp) with h624 | h624
                            · rcases p621_3 (m.d 0 2) (by simp) with h625 | h625
                              · linarith only [h0, h625, hlam]
                              · linarith only [h4, h625, hlam]
                            · linarith only [h1, h624, hlam]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h0, h5, h611, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p621_1]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            rcases p621_3 (m.d 0 1) (by simp) with h630 | h630
                            · rcases p621_3 (m.d 0 2) (by simp) with h631 | h631
                              · linarith only [h0, h631, hlam]
                              · linarith only [h560, h631, hlam]
                            · linarith only [h3, h630, hlam]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h0, hlam, p621_1]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [hlam, p621_0]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p621_1, u2elo3]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h5, hlam, p621_1]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h5, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p621_1, u2elo3]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h1, hlam, p621_1]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h4, hlam, p621_0]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [hlam, p621_0]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h561, hlam, p621_0]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h563, hlam, p621_1]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h2, hlam, p621_1]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h0, h611, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p621_1]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p621_1, u2elo3]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [hlam, p621_0]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h3, h5, h615, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p621_1, u2elo3]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h3, hlam, p621_1]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h560, hlam, p621_0]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h1, h560, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p621_1, u2elo0]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [h610, hlam, p621_0]
                          · have p621_0 := h621c.1
                            have p621_1 := h621c.2.1
                            have p621_2 := h621c.2.2.1
                            have p621_3 := h621c.2.2.2
                            linarith only [hlam, p621_0]
                        · linarith only [h5, h617, h619, h620, hc02, hlam, hphi, u2elo4]
                      · linarith only [h5, h560, h610, h619, hlam]
                · linarith only [h5, h560, h611, h614, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h4, h5, h611, hc12, hlam, hphi, u2elo3]
          · linarith only [h5, h560, h610, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h660 | h660
      · linarith only [h4, h5, h660, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h662 | h662
        · linarith only [h4, h560, h662, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h664 | h664
          · rcases m.htr 1 2 3 (by decide) (by decide) with h665 | h665
            · rcases m.htr 1 2 4 (by decide) (by decide) with h666 | h666
              · linarith only [h0, h5, h666, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h668 | h668
                · linarith only [h0, h560, h668, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h670 | h670
                  · linarith only [h1, h662, h670, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                    · linarith only [h0, h560, h660, h664, h665, h672, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h674 | h674
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h675 | h675
                        · rcases h0bigk with h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h0, h665, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            rcases p676_3 (m.d 0 1) (by simp) with h679 | h679
                            · rcases p676_3 (m.d 0 2) (by simp) with h680 | h680
                              · linarith only [h0, h680, hlam]
                              · linarith only [h4, h680, hlam]
                            · linarith only [h1, h679, hlam]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h0, h560, h664, h665, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h0, h560, h665, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h0, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h560, h674, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p676_1, u2elo3]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h5, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h560, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h1, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h4, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h660, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h662, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h2, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p676_1, u2elo3]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h4, h5, h560, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p676_1, u2elo3]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h3, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h4, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h1, h560, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p676_1, u2elo4]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h664, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hlam, p676_0]
                        · linarith only [h5, h664, h672, h675, hlam]
                      · linarith only [h5, h664, h674, hlam]
            · linarith only [h4, h665, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h709 | h709
            · rcases m.htr 1 2 4 (by decide) (by decide) with h710 | h710
              · linarith only [h5, h710, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h712 | h712
                · linarith only [h0, h560, h712, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h714 | h714
                  · linarith only [h1, h662, h714, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h716 | h716
                    · linarith only [h0, h5, h709, h716, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h718 | h718
                      · linarith only [h0, h5, h664, h709, h718, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h5, h709, h718, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4, h5, h709, hc12, hlam, hphi, u2elo3]

end R2N4
