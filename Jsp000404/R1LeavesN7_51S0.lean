import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h3 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
  · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
    · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
      · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
        · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
          · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
            · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h12, h4, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h11, h12, h4, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h11, h15, h4, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · rcases h5bigk with h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [hlam, p17_0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p17_1, u2elo0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h1, h11, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17_1, u2elo0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h1, h15, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17_1, u2elo0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p17_1, u2elo0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h0, hlam, p17_0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [hlam, p17_0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h0, h11, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p17_1]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h0, h1, h15, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17_1, u2elo0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h4, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p17_1, u2elo1]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h1, hlam, p17_1]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h5, hlam, p17_1]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [hlam, p17_0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h15, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17_1, u2elo4]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h11, hlam, p17_0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h2, hlam, p17_1]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h7, hlam, p17_1]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h10, hlam, p17_0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [hlam, p17_0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h15, hlam, p17_0]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h3, hlam, p17_1]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h8, hlam, p17_1]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h3, hc04, hc25, hlam, hphi, ht0b, ht5b, p17_1]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [h15, h4, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17_1, u2elo1]
                    · have p17_0 := h17c.1
                      have p17_1 := h17c.2.1
                      have p17_2 := h17c.2.2.1
                      have p17_3 := h17c.2.2.2
                      linarith only [hlam, p17_0]
              · linarith only [h10, h4, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
              · linarith only [h4, h44, h6, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
                · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                  · rcases h5bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [hlam, p48_0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h1, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p48_1, u2elo0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo0]
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
                      linarith only [h0, h44, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h0, h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h4, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h1, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h5, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [hlam, p48_0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h44, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo4]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h2, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h7, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h2, hc03, hc25, hlam, hphi, ht0b, ht5b, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [hlam, p48_0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h4, h47, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h3, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h8, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h46, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h47, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [hlam, p48_0]
                  · linarith only [h4, h47, h6, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                  · linarith only [h4, h46, h6, h75, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h4, h6, h75, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
            · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
              · rcases m.htr 2 4 5 (by decide) (by decide) with h80 | h80
                · linarith only [h4, h78, h8, h80, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h6, h8, h82, hlam]
                  · rcases h5bigk with h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [hlam, p84_0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p84_1, u2elo0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p84_1, u2elo0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p84_1, u2elo0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h1, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p84_1, u2elo0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h0, hlam, p84_0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [hlam, p84_0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h0, h79, hc01, hc35, hlam, hphi, ht0b, ht5b, p84_1]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h0, h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p84_1, u2elo0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h8, hlam, p84_0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h1, hlam, p84_1]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h5, hlam, p84_1]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [hlam, p84_0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p84_1, u2elo4]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h80, hlam, p84_0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h2, hlam, p84_1]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h7, hlam, p84_1]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h79, hlam, p84_0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [hlam, p84_0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h82, hlam, p84_0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h3, hlam, p84_1]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h3, hc04, hc15, hlam, hphi, ht0b, ht5b, p84_1]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h1, h3, h79, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p84_1, u2elo0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [h1, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p84_1, u2elo0]
                    · have p84_0 := h84c.1
                      have p84_1 := h84c.2.1
                      have p84_2 := h84c.2.2.1
                      have p84_3 := h84c.2.2.2
                      linarith only [hlam, p84_0]
              · linarith only [h4, h7, h78, h79, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
              · linarith only [h111, h4, h6, h78, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h113 | h113
                · linarith only [h113, h6, h78, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                  · linarith only [h115, h6, h8, hlam]
                  · rcases h5bigk with h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [hlam, p117_0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p117_1, u2elo0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p117_1, u2elo0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p117_1, u2elo0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h1, h6, h78, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p117_1, u2elo0]
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
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p117_1]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h0, h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p117_1, u2elo0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h8, hlam, p117_0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h1, hlam, p117_1]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h5, hlam, p117_1]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [hlam, p117_0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h111, hlam, p117_1]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h113, hlam, p117_0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h2, hlam, p117_1]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h7, hlam, p117_1]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h2, hc03, hc25, hlam, hphi, ht0b, ht5b, p117_1]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [hlam, p117_0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h115, hlam, p117_0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h3, hlam, p117_1]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h1, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p117_1, u2elo0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h1, h111, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p117_1, u2elo0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [h1, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p117_1, u2elo0]
                    · have p117_0 := h117c.1
                      have p117_1 := h117c.2.1
                      have p117_2 := h117c.2.2.1
                      have p117_3 := h117c.2.2.2
                      linarith only [hlam, p117_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
          · linarith only [h143, h6, h7, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
            · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
              · linarith only [h146, h4, h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h148 | h148
                · linarith only [h143, h145, h148, h4, h7, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h150 | h150
                  · linarith only [h143, h145, h150, h4, h7, hlam]
                  · rcases h5bigk with h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [hlam, p152_0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h1, h145, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p152_1, u2elo0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p152_1, u2elo0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h1, h145, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p152_1, u2elo0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h1, h145, h150, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p152_1, u2elo0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h0, hlam, p152_0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [hlam, p152_0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p152_1]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h7, hlam, p152_0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h143, hlam, p152_0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h1, hlam, p152_1]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h5, hlam, p152_1]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [hlam, p152_0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h146, hlam, p152_1]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h148, hlam, p152_0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h2, hlam, p152_1]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h2, hc03, hc15, hlam, hphi, ht0b, ht5b, p152_1]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h1, h150, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p152_1, u2elo0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [hlam, p152_0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h150, hlam, p152_0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h3, hlam, p152_1]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h1, h145, h3, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p152_1, u2elo0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h1, h145, h146, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p152_1, u2elo0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [h1, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p152_1, u2elo0]
                    · have p152_0 := h152c.1
                      have p152_1 := h152c.2.1
                      have p152_2 := h152c.2.2.1
                      have p152_3 := h152c.2.2.2
                      linarith only [hlam, p152_0]
            · linarith only [h145, h6, h7, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h179 | h179
        · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
          · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
            · linarith only [h179, h181, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
              · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                · rcases m.htr 3 4 5 (by decide) (by decide) with h185 | h185
                  · rcases h5bigk with h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [hlam, p186_0]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo0]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo0]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h1, h185, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo0]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo0]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h0, hlam, p186_0]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [hlam, p186_0]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h179, h185, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h179, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h1, hlam, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h5, hlam, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [hlam, p186_0]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h185, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo4]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h183, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo2]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h2, hlam, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h179, hlam, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h183, hlam, p186_0]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [hlam, p186_0]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h2, hc03, hc45, hlam, hphi, ht0b, ht5b, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h3, hlam, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h180, hlam, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h184, hlam, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [h185, hlam, p186_1]
                    · have p186_0 := h186c.1
                      have p186_1 := h186c.2.1
                      have p186_2 := h186c.2.2.1
                      have p186_3 := h186c.2.2.2
                      linarith only [hlam, p186_0]
                  · linarith only [h1, h183, h185, h3, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                · linarith only [h181, h183, h184, hlam]
              · linarith only [h179, h183, h6, hc23, hc34, hlam, hphi]
          · linarith only [h179, h180, h6, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h216 | h216
          · rcases m.htr 2 3 4 (by decide) (by decide) with h217 | h217
            · linarith only [h216, h217, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h219 | h219
              · linarith only [h179, h219, h4, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h221 | h221
                · rcases m.htr 3 4 5 (by decide) (by decide) with h222 | h222
                  · rcases h5bigk with h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [hlam, p223_0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h1, h179, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p223_1, u2elo0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h1, h219, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p223_1, u2elo0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h1, h179, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p223_1, u2elo0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p223_1, u2elo0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h0, hlam, p223_0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [hlam, p223_0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h0, h219, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p223_1]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h179, hlam, p223_0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p223_1]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h1, hlam, p223_1]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h5, hlam, p223_1]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [hlam, p223_0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h219, hlam, p223_1]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p223_1, u2elo4]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h2, hlam, p223_1]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h1, h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p223_1, u2elo0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h1, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p223_1, u2elo0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [hlam, p223_0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h1, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p223_1, u2elo0]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h3, hlam, p223_1]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h216, hlam, p223_1]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h221, hlam, p223_1]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [h222, hlam, p223_1]
                    · have p223_0 := h223c.1
                      have p223_1 := h223c.2.1
                      have p223_2 := h223c.2.2.1
                      have p223_3 := h223c.2.2.2
                      linarith only [hlam, p223_0]
                  · linarith only [h221, h222, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h250 | h250
                  · rcases h5bigk with h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [hlam, p251_0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h1, h216, h217, h221, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p251_1, u2elo0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h1, h217, h221, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p251_1, u2elo0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p251_1, u2elo0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h1, h217, h221, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p251_1, u2elo0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h0, hlam, p251_0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [hlam, p251_0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h0, h217, h221, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p251_1]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h179, hlam, p251_0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h1, h179, h2, h217, h221, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p251_1, u2elo0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h1, hlam, p251_1]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h5, hlam, p251_1]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [hlam, p251_0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h219, hlam, p251_1]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h221, hlam, p251_0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h2, hlam, p251_1]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h1, h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p251_1, u2elo0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h1, h2, h217, h221, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p251_1, u2elo0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [hlam, p251_0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h1, h2, h217, h221, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p251_1, u2elo0]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h3, hlam, p251_1]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h216, hlam, p251_1]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h217, h221, hc23, hc45, hlam, hphi, ht34, p251_1]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [h250, hlam, p251_1]
                    · have p251_0 := h251c.1
                      have p251_1 := h251c.2.1
                      have p251_2 := h251c.2.2.1
                      have p251_3 := h251c.2.2.2
                      linarith only [hlam, p251_0]
                  · linarith only [h216, h250, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
            · linarith only [h278, h4, h6, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h280 | h280
              · linarith only [h179, h280, h4, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h282 | h282
                · linarith only [h216, h282, h5, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                  · rcases h5bigk with h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [hlam, p285_0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p285_1, u2elo0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p285_1, u2elo0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h1, h282, h284, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p285_1, u2elo0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h1, h282, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p285_1, u2elo0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h0, hlam, p285_0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [hlam, p285_0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p285_1]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h179, hlam, p285_0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h216, hlam, p285_0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h1, hlam, p285_1]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h5, hlam, p285_1]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [hlam, p285_0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h280, hlam, p285_1]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h282, hlam, p285_0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h2, hlam, p285_1]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h2, hc03, hc15, hlam, hphi, ht0b, ht5b, p285_1]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h1, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p285_1, u2elo0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [hlam, p285_0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h1, h2, h216, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p285_1, u2elo0]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h3, hlam, p285_1]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h216, h284, h4, h6, hc23, hc34, hlam, hphi, p285_1]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h278, h282, h284, hc23, hc34, hlam, hphi, p285_1]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [h284, hlam, p285_1]
                    · have p285_0 := h285c.1
                      have p285_1 := h285c.2.1
                      have p285_2 := h285c.2.2.1
                      have p285_3 := h285c.2.2.2
                      linarith only [hlam, p285_0]
                  · rcases h5bigk with h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [hlam, p311_0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h1, h216, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p311_1, u2elo0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h1, h278, h282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p311_1, u2elo0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p311_1, u2elo0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p311_1, u2elo0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h0, hlam, p311_0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [hlam, p311_0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h0, h278, h282, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p311_1]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h179, hlam, p311_0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h216, hlam, p311_0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h1, hlam, p311_1]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h5, hlam, p311_1]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [hlam, p311_0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h280, hlam, p311_1]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h282, hlam, p311_0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h2, hlam, p311_1]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h2, hc03, hc15, hlam, hphi, ht0b, ht5b, p311_1]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h1, h2, h278, h282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p311_1, u2elo0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [hlam, p311_0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h284, hlam, p311_0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h3, hlam, p311_1]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h278, h282, h5, hc23, hc45, hlam, hphi, ht34, p311_1]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h1, h278, h282, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p311_1, u2elo0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [h1, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p311_1, u2elo0]
                    · have p311_0 := h311c.1
                      have p311_1 := h311c.2.1
                      have p311_2 := h311c.2.2.1
                      have p311_3 := h311c.2.2.2
                      linarith only [hlam, p311_0]
    · linarith only [h1, h5, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h338 | h338
    · rcases m.htr 1 3 4 (by decide) (by decide) with h339 | h339
      · rcases m.htr 1 3 5 (by decide) (by decide) with h340 | h340
        · rcases m.htr 1 4 5 (by decide) (by decide) with h341 | h341
          · rcases m.htr 2 3 4 (by decide) (by decide) with h342 | h342
            · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
              · rcases m.htr 2 4 5 (by decide) (by decide) with h344 | h344
                · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
                  · rcases h5bigk with h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p346_1, u2elo0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h1, h343, h345, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p346_1, u2elo0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h1, h345, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p346_1, u2elo0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p346_1, u2elo0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h0, hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h0, h343, h345, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h338, h345, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p346_1, u2elo2]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h338, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p346_1, u2elo2]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h1, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h338, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h345, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p346_1, u2elo4]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h338, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p346_1, u2elo2]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h2, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h340, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h343, hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h2, hc03, hc45, hlam, hphi, ht0b, ht5b, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h3, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h341, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h344, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h345, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hlam, p346_0]
                  · linarith only [h338, h344, h345, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h373 | h373
                  · linarith only [h342, h344, h373, hlam]
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
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p375_1, u2elo0]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p375_1, u2elo0]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p375_1, u2elo0]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h1, h342, h344, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p375_1, u2elo0]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h0, hlam, p375_0]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [hlam, p375_0]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h0, h343, hc01, hc35, hlam, hphi, ht0b, ht5b, p375_1]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h338, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p375_1, u2elo2]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h338, h342, h344, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p375_1, u2elo2]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h1, hlam, p375_1]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h338, hlam, p375_1]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [hlam, p375_0]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p375_1, u2elo4]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h344, hlam, p375_0]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h2, hlam, p375_1]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h340, hlam, p375_1]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h343, hlam, p375_0]
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
                      linarith only [h3, hlam, p375_1]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h341, hlam, p375_1]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h3, hc04, hc25, hlam, hphi, ht0b, ht5b, p375_1]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [h339, h341, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p375_1, u2elo2]
                    · have p375_0 := h375c.1
                      have p375_1 := h375c.2.1
                      have p375_2 := h375c.2.2.1
                      have p375_3 := h375c.2.2.2
                      linarith only [hlam, p375_0]
              · linarith only [h1, h2, h343, h4, hc12, hlam, hphi, u2elo0]
            · linarith only [h339, h342, h4, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h403 | h403
            · rcases m.htr 2 3 5 (by decide) (by decide) with h404 | h404
              · rcases m.htr 2 4 5 (by decide) (by decide) with h405 | h405
                · linarith only [h338, h339, h341, h4, h405, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h407 | h407
                  · linarith only [h339, h341, h407, hlam]
                  · rcases h5bigk with h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p409_1, u2elo0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p409_1, u2elo0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h1, h407, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p409_1, u2elo0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h1, h339, h341, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p409_1, u2elo0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h0, hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h338, h4, h407, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p409_1, u2elo2]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h341, hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h1, hlam, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h338, hlam, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h407, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p409_1, u2elo4]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h405, hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h2, hlam, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h340, hlam, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h404, hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h407, hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h3, hlam, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h3, hc04, hc15, hlam, hphi, ht0b, ht5b, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h1, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p409_1, u2elo0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h1, h3, h407, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p409_1, u2elo0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hlam, p409_0]
              · linarith only [h1, h2, h4, h404, hc12, hlam, hphi, u2elo0]
            · linarith only [h339, h4, h403, hlam]
        · linarith only [h338, h340, h4, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h438 | h438
        · rcases m.htr 1 4 5 (by decide) (by decide) with h439 | h439
          · rcases m.htr 2 3 4 (by decide) (by decide) with h440 | h440
            · linarith only [h339, h4, h440, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h442 | h442
              · rcases m.htr 2 4 5 (by decide) (by decide) with h443 | h443
                · rcases m.htr 3 4 5 (by decide) (by decide) with h444 | h444
                  · rcases h5bigk with h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p445_1, u2elo0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h1, h442, h444, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p445_1, u2elo0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h1, h444, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p445_1, u2elo0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p445_1, u2elo0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h0, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h0, h442, h444, hc01, hc45, hlam, hphi, ht0b, ht5b, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h338, h444, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p445_1, u2elo1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h338, h4, h440, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h1, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h338, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h444, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p445_1, u2elo4]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h338, h4, h440, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h2, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h438, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h442, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h2, hc03, hc45, hlam, hphi, ht0b, ht5b, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h3, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h439, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h443, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h444, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                  · linarith only [h4, h440, h444, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h338, h4, h439, h440, h443, hlam]
              · linarith only [h2, h338, h4, h442, hc03, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h338, h339, h4, h439, hlam]
        · linarith only [h338, h4, h438, hlam]
    · linarith only [h1, h338, hc12, hlam, hphi, u2elo0]

end R2N4
