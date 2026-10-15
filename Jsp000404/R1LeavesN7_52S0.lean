import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
  · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
        · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
          · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                  · rcases h0emin with h15 | h15 | h15 | h15 | h15
                    · rcases h5bigk with h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h3, h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h3, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h3, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h3, h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h2, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p16_1]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h2, h3, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h2, h3, h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h4, hlam, p16_1]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h9, hlam, p16_1]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p16_1, u2elo4]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h0, h13, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h6, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h11, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h13, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h3, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h7, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h12, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h3, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h14, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hlam, p16_0]
                    · linarith only [h15, hlam, ht01, ht12, u2elo0]
                    · linarith only [h15, h3, hlam, ht01, ht12, u2elo0]
                    · linarith only [h15, h3, h5, hlam, ht01, ht12, u2elo0]
                    · linarith only [h15, h3, h5, h7, hlam, ht01, ht12, u2elo0]
                  · rcases h0emin with h46 | h46 | h46 | h46 | h46
                    · rcases h5bigk with h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h3, h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p47_1, u2elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h3, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p47_1, u2elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h3, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p47_1, u2elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h14, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p47_1, u2elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h2, hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h13, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p47_1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h2, h3, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p47_1, u2elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h14, h2, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p47_1, u2elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h4, hlam, p47_1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h9, hlam, p47_1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p47_1, u2elo4]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h0, h13, h14, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p47_1, u2elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h6, hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h11, hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h13, hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h14, hlam, p47_1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h7, hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h12, hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h3, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p47_1, u2elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h1, h10, h12, h14, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p47_1, u2elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hlam, p47_0]
                    · linarith only [h46, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h46, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h46, h5, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h46, h5, h7, hlam, ht01, ht12, u2elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                  · rcases h0emin with h78 | h78 | h78 | h78 | h78
                    · rcases h5bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h3, h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h13, h3, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h3, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h3, h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h2, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h13, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p79_1]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h2, h3, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h2, h3, h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h4, hlam, p79_1]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h9, hlam, p79_1]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h13, hlam, p79_1]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo4]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h6, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h11, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h3, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h1, h10, h3, h77, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h7, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h12, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h13, hc23, hc45, hlam, hphi, ht34, p79_1]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h77, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hlam, p79_0]
                    · linarith only [h78, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h78, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h5, h78, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h5, h7, h78, hlam, ht01, ht12, u2elo0]
                  · rcases h0emin with h109 | h109 | h109 | h109 | h109
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
                        linarith only [h3, h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h13, h3, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h3, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h3, h5, h7, h77, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p110_1, u2elo0]
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
                        linarith only [h13, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h2, h3, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h2, h3, h5, h7, h77, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p110_1, u2elo0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h4, hlam, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h9, hlam, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h13, hlam, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h13, h77, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo4]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h6, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h11, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h3, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h77, hlam, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h7, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h12, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h1, h10, h12, h13, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h1, h10, h12, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [hlam, p110_0]
                    · linarith only [h109, hlam, ht01, ht12, u2elo0]
                    · linarith only [h109, h3, hlam, ht01, ht12, u2elo0]
                    · linarith only [h109, h3, h5, hlam, ht01, ht12, u2elo0]
                    · linarith only [h109, h3, h5, h7, hlam, ht01, ht12, u2elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                  · linarith only [h12, h141, h3, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases h0emin with h143 | h143 | h143 | h143 | h143
                    · rcases h5bigk with h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [hlam, p144_0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h3, h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h3, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h141, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h10, h12, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h2, hlam, p144_0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [hlam, p144_0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p144_1]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h141, h2, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h12, hlam, p144_1]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h4, hlam, p144_1]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h9, hlam, p144_1]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [hlam, p144_0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h141, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo4]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h12, h9, hlam, p144_1]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h6, hlam, p144_0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h11, hlam, p144_0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h140, hlam, p144_0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [hlam, p144_0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h141, hlam, p144_1]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h7, hlam, p144_0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h3, h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h140, h141, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [h141, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo0]
                      · have p144_0 := h144c.1
                        have p144_1 := h144c.2.1
                        have p144_2 := h144c.2.2.1
                        have p144_3 := h144c.2.2.2
                        linarith only [hlam, p144_0]
                    · linarith only [h143, hlam, ht01, ht12, u2elo0]
                    · linarith only [h143, h3, hlam, ht01, ht12, u2elo0]
                    · linarith only [h143, h3, h5, hlam, ht01, ht12, u2elo0]
                    · linarith only [h143, h3, h5, h7, hlam, ht01, ht12, u2elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h174 | h174
                  · linarith only [h10, h12, h174, hlam]
                  · rcases h0emin with h176 | h176 | h176 | h176 | h176
                    · rcases h5bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h11, h140, h3, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u2elo0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h3, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p177_1, u2elo0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h140, h3, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u2elo0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h12, h3, h5, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p177_1, u2elo0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h2, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p177_1]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h140, h2, h3, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u2elo0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h12, hlam, p177_1]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h4, hlam, p177_1]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h9, hlam, p177_1]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h140, hlam, p177_1]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h12, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p177_1, u2elo4]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h6, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h11, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h11, h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p177_1]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h174, hlam, p177_1]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h7, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h3, h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p177_1, u2elo0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h140, h3, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u2elo0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h3, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p177_1, u2elo0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hlam, p177_0]
                    · linarith only [h176, hlam, ht01, ht12, u2elo0]
                    · linarith only [h176, h3, hlam, ht01, ht12, u2elo0]
                    · linarith only [h176, h3, h5, hlam, ht01, ht12, u2elo0]
                    · linarith only [h176, h3, h5, h7, hlam, ht01, ht12, u2elo0]
            · linarith only [h10, h11, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h208 | h208
            · linarith only [h10, h208, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
              · rcases m.htr 2 3 5 (by decide) (by decide) with h211 | h211
                · linarith only [h208, h211, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h213 | h213
                  · rcases h0emin with h214 | h214 | h214 | h214 | h214
                    · rcases h5bigk with h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [hlam, p215_0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h3, h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p215_1, u2elo0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h3, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p215_1, u2elo0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h208, h3, h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p215_1, u2elo0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h3, h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p215_1, u2elo0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h2, hlam, p215_0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [hlam, p215_0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p215_1]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h208, hlam, p215_1]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h10, h210, h3, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p215_1, u2elo0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h4, hlam, p215_1]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h9, hlam, p215_1]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [hlam, p215_0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h211, hlam, p215_1]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p215_1, u2elo4]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h6, hlam, p215_0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h213, h3, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p215_1, u2elo0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h213, h3, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p215_1, u2elo0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [hlam, p215_0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h213, h3, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p215_1, u2elo0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h7, hlam, p215_0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h210, hlam, p215_0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h211, hc23, hc45, hlam, hphi, ht34, p215_1]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [h213, hlam, p215_0]
                      · have p215_0 := h215c.1
                        have p215_1 := h215c.2.1
                        have p215_2 := h215c.2.2.1
                        have p215_3 := h215c.2.2.2
                        linarith only [hlam, p215_0]
                    · linarith only [h214, hlam, ht01, ht12, u2elo0]
                    · linarith only [h214, h3, hlam, ht01, ht12, u2elo0]
                    · linarith only [h214, h3, h5, hlam, ht01, ht12, u2elo0]
                    · linarith only [h214, h3, h5, h7, hlam, ht01, ht12, u2elo0]
                  · linarith only [h10, h213, h3, h5, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                · linarith only [h10, h246, h3, h5, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                  · linarith only [h10, h210, h248, h3, h5, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h10, h248, h3, h5, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
        · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
      · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h253 | h253
      · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
        · rcases m.htr 1 3 4 (by decide) (by decide) with h255 | h255
          · rcases m.htr 1 3 5 (by decide) (by decide) with h256 | h256
            · rcases m.htr 1 4 5 (by decide) (by decide) with h257 | h257
              · linarith only [h2, h257, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                · rcases m.htr 3 4 5 (by decide) (by decide) with h260 | h260
                  · linarith only [h260, h5, h7, hlam]
                  · rcases h0emin with h262 | h262 | h262 | h262 | h262
                    · rcases h5bigk with h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [hlam, p263_0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h254, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p263_1, u2elo0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p263_1, u2elo0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h260, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p263_1, u2elo0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h7, hlam, p263_1]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h2, hlam, p263_0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [hlam, p263_0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p263_1]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h2, h260, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p263_1, u2elo0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h257, hlam, p263_1]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h4, hlam, p263_1]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h254, hlam, p263_1]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [hlam, p263_0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h260, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p263_1, u2elo4]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h0, h253, h257, h259, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p263_1, u2elo0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h6, hlam, p263_0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h256, hlam, p263_0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h259, hlam, p263_0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [hlam, p263_0]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h260, hlam, p263_1]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h260, h6, hc34, hc45, hlam, hphi, p263_1]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h256, h260, hc34, hc45, hlam, hphi, p263_1]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h259, h260, hc34, hc45, hlam, hphi, p263_1]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [h260, hc34, hc45, hlam, hphi, p263_1]
                      · have p263_0 := h263c.1
                        have p263_1 := h263c.2.1
                        have p263_2 := h263c.2.2.1
                        have p263_3 := h263c.2.2.2
                        linarith only [hlam, p263_0]
                    · linarith only [h262, hlam, ht01, ht12, u2elo0]
                    · linarith only [h262, h3, hlam, ht01, ht12, u2elo0]
                    · linarith only [h262, h3, h5, hlam, ht01, ht12, u2elo0]
                    · linarith only [h262, h4, hlam, ht01, ht12, u2elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h293 | h293
                  · linarith only [h293, h3, h5, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases h0emin with h295 | h295 | h295 | h295 | h295
                    · rcases h5bigk with h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [hlam, p296_0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h257, h3, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p296_1, u2elo0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h3, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p296_1, u2elo0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h259, h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p296_1, u2elo0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h7, hlam, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h2, hlam, p296_0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [hlam, p296_0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h2, h259, h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p296_1, u2elo0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h257, hlam, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h4, hlam, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h254, hlam, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [hlam, p296_0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h259, hlam, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h7, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p296_1, u2elo4]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h6, hlam, p296_0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h256, hlam, p296_0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h3, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p296_1, u2elo0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [hlam, p296_0]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h293, hlam, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h5, h7, hc34, hc45, hlam, hphi, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h255, h257, hc34, hc45, hlam, hphi, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h259, hc23, hc45, hlam, hphi, ht34, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [h259, hc23, hc45, hlam, hphi, ht34, p296_1]
                      · have p296_0 := h296c.1
                        have p296_1 := h296c.2.1
                        have p296_2 := h296c.2.2.1
                        have p296_3 := h296c.2.2.2
                        linarith only [hlam, p296_0]
                    · linarith only [h295, hlam, ht01, ht12, u2elo0]
                    · linarith only [h295, h3, hlam, ht01, ht12, u2elo0]
                    · linarith only [h295, h3, h5, hlam, ht01, ht12, u2elo0]
                    · linarith only [h295, h4, hlam, ht01, ht12, u2elo0]
            · linarith only [h255, h256, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h327 | h327
            · linarith only [h255, h3, h327, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h329 | h329
              · linarith only [h255, h3, h329, h5, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                · linarith only [h3, h327, h331, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h333 | h333
                  · linarith only [h333, h5, h7, hlam]
                  · rcases h0emin with h335 | h335 | h335 | h335 | h335
                    · rcases h5bigk with h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h3, h329, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p336_1, u2elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h3, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p336_1, u2elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h3, h333, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p336_1, u2elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h7, hlam, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h2, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h327, hlam, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h329, hlam, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h4, hlam, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h254, hlam, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h331, hlam, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h7, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p336_1, u2elo4]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h6, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h3, h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p336_1, u2elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h3, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p336_1, u2elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h333, hlam, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h2, h253, h255, h329, hc23, hc45, hlam, hphi, ht34, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h253, h255, h329, hc23, hc45, hlam, hphi, ht34, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h331, hc23, hc45, hlam, hphi, ht34, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h253, h327, hc23, hc45, hlam, hphi, ht34, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [hlam, p336_0]
                    · linarith only [h335, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h335, hlam, ht01, ht12, u2elo0]
                    · linarith only [h335, h4, h7, hlam, ht01, ht12, u2elo0]
                    · linarith only [h335, h4, hlam, ht01, ht12, u2elo0]
        · linarith only [h254, h4, hc12, hlam, hphi, u2elo0]
      · linarith only [h253, h3, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h368 | h368
    · linarith only [h368, h5, h6, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
      · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
        · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
          · rcases m.htr 1 3 5 (by decide) (by decide) with h373 | h373
            · linarith only [h1, h373, h6, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
              · linarith only [h2, h368, h372, h373, h375, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h377 | h377
                · linarith only [h3, h377, h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
                  · linarith only [h368, h379, h5, hlam]
                  · rcases h0emin with h381 | h381 | h381 | h381 | h381
                    · rcases h5bigk with h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [hlam, p382_0]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h372, h373, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h377, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p382_1, u2elo0]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h6, hlam, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h368, hlam, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h2, hlam, p382_0]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [hlam, p382_0]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h371, h377, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p382_1, u2elo1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h373, hlam, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h375, hlam, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h4, hlam, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h371, hlam, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [hlam, p382_0]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h377, hlam, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h1, h372, h379, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p382_1, u2elo4]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h1, h372, h379, h6, hc34, hc45, hlam, hphi, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h372, h373, h379, hc34, hc45, hlam, hphi, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h377, h379, hc23, hc45, hlam, hphi, ht34, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [hlam, p382_0]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h379, hlam, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h1, h372, h6, hc34, hc45, hlam, hphi, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h372, h373, hc34, hc45, hlam, hphi, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h377, hc23, hc45, hlam, hphi, ht34, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [h1, h372, h6, hc34, hc45, hlam, hphi, p382_1]
                      · have p382_0 := h382c.1
                        have p382_1 := h382c.2.1
                        have p382_2 := h382c.2.2.1
                        have p382_3 := h382c.2.2.2
                        linarith only [hlam, p382_0]
                    · linarith only [h381, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h381, hlam, ht01, ht12, u2elo0]
                    · linarith only [h381, h4, h5, h6, hlam, ht01, ht12, u2elo0]
                    · linarith only [h381, h4, hlam, ht01, ht12, u2elo0]
          · linarith only [h372, h5, h6, hc13, hc35, hlam, hphi]
        · linarith only [h371, h4, hc12, hlam, hphi, u2elo0]
      · linarith only [h3, h370, hc12, hlam, hphi, u2elo0]

end R2N4
