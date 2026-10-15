import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_23_L_0_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0elo := hb0.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
                · linarith only [h0, h3, h6, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases h3bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h0, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u0elo0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h0, h7, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1, u0elo0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1, u0elo0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h0, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1, u0elo0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h0, hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h7, h8, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1, u0elo0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h0, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1, u0elo0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h1, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10_1]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h3, hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h0, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1, u0elo2]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h0, h3, hc35, hlam, hphi, ht0b, ht5b, p10_1, u0elo0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h1, hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h4, hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h6, hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h8, hlam, p10_1]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h2, hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h5, hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h7, hlam, p10_0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [h0, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1, u0elo0]
                  · have p10_0 := h10c.1
                    have p10_1 := h10c.2.1
                    have p10_2 := h10c.2.2.1
                    have p10_3 := h10c.2.2.2
                    linarith only [hlam, p10_0]
              · linarith only [h0, h5, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h4, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h0, h2, h4, h5, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
          · linarith only [h0, h1, h39, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
            · linarith only [h3, h4, h41, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
              · linarith only [h3, h39, h43, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                · rcases h3bigk with h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h0, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h0, h39, h45, hc15, hlam, hphi, ht0b, ht5b, p46_1, u0elo0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h0, h39, hc15, hlam, hphi, ht0b, ht5b, p46_1, u0elo0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h0, hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h4, hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h39, hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h1, h3, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46_1]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h3, hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h41, hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h43, hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h1, hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [hc13, hc34, hlam, hphi, p46_1]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo2]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h0, h1, h3, h39, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h2, hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h3, hc23, hc35, hlam, hphi, p46_1]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h0, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [h45, hlam, p46_0]
                  · have p46_0 := h46c.1
                    have p46_1 := h46c.2.1
                    have p46_2 := h46c.2.2.1
                    have p46_3 := h46c.2.2.2
                    linarith only [hlam, p46_0]
                · rcases h3bigk with h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1, u0elo0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1, u0elo0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, h4, hc14, hlam, hphi, ht0b, ht45, ht5b, p72_1, u0elo0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, h43, hc25, hlam, hphi, ht0b, ht5b, p72_1, u0elo0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1, u0elo0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h4, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h39, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h3, h4, hc03, hc34, hlam, hphi, p72_1]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h3, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h41, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h43, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h1, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hc13, hc34, hlam, hphi, p72_1]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1, u0elo2]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h45, hlam, p72_1]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h2, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, h2, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1, u0elo0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1, u0elo0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, p72_1, u0elo0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hlam, p72_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
        · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
          · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
            · rcases m.htr 2 3 5 (by decide) (by decide) with h101 | h101
              · rcases m.htr 3 4 5 (by decide) (by decide) with h102 | h102
                · linarith only [h0, h102, h98, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases h3bigk with h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h0, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p104_1, u0elo0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p104_1, u0elo0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p104_1, u0elo0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h0, h102, hc34, hlam, hphi, ht0b, ht45, ht5b, p104_1, u0elo0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h0, hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h3, hlam, p104_1]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p104_1, u0elo0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h0, h102, hc34, hlam, hphi, ht0b, ht45, ht5b, p104_1, u0elo0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h1, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p104_1]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h3, hc12, hc23, hlam, hphi, p104_1]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    rcases p104_3 (m.d 0 3) (by simp) with h118 | h118
                    · linarith only [h118, hc34, hlam, hphi, ht0b, ht45, ht5b, p104_1, u0elo2]
                    · linarith only [h1, h118, hlam]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    rcases p104_3 (m.d 0 3) (by simp) with h121 | h121
                    · linarith only [h0, h102, h121, hc34, hlam, hphi, ht0b, ht45, ht5b, p104_1, u0elo0]
                    · linarith only [h121, h2, hlam]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h1, hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h98, hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h100, hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h102, hlam, p104_1]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h2, hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h99, hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h101, hlam, p104_0]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [h99, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p104_1]
                  · have p104_0 := h104c.1
                    have p104_1 := h104c.2.1
                    have p104_2 := h104c.2.2.1
                    have p104_3 := h104c.2.2.2
                    linarith only [hlam, p104_0]
              · linarith only [h0, h101, h99, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h1, h100, h3, h99, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
          · linarith only [h0, h2, h98, h99, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
          · linarith only [h0, h1, h137, h98, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h139 | h139
            · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
              · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                · rcases h3bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h0, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u0elo0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u0elo0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h0, h141, hc45, hlam, hphi, ht0b, ht5b, p142_1, u0elo0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p142_1, u0elo0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h0, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h3, hlam, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h98, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h137, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h0, h3, hc12, hc23, hlam, hphi, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h3, hc12, hc23, hlam, hphi, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h137, h141, h3, hc12, hc23, hlam, hphi, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h137, h3, hc12, hc23, hlam, hphi, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h1, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h1, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo2]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h139, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h0, h1, h137, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h2, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h3, hc12, hc35, hlam, hphi, ht23, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h140, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h141, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, p142_0]
                · rcases h3bigk with h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1, u0elo0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p168_1, u0elo0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p168_1, u0elo0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p168_1, u0elo0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h0, hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h3, hlam, p168_1]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h98, hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h137, hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h0, h3, hc12, hc23, hlam, hphi, p168_1]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h3, hc12, hc23, hlam, hphi, p168_1]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h3, h98, hc12, hc23, hlam, hphi, p168_1]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h141, h3, h98, hc12, hc23, hlam, hphi, p168_1]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h1, hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h141, h2, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1, u0elo2]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h139, hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h141, hlam, p168_1]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h2, hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h0, h2, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1, u0elo0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h140, hlam, p168_0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [h0, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, p168_1, u0elo0]
                  · have p168_0 := h168c.1
                    have p168_1 := h168c.2.1
                    have p168_2 := h168c.2.2.1
                    have p168_3 := h168c.2.2.2
                    linarith only [hlam, p168_0]
              · linarith only [h0, h140, h2, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h1, h139, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h196 | h196
      · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
        · rcases m.htr 1 3 5 (by decide) (by decide) with h198 | h198
          · linarith only [h0, h198, h2, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
            · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
              · linarith only [h0, h196, h2, h201, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                · linarith only [h0, h196, h200, h203, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases h3bigk with h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p205_1, u0elo2]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h2, h200, h203, hc34, hc45, hlam, hphi, p205_1]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h2, h203, hc34, hc45, hlam, hphi, p205_1]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h2, hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h0, hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h0, h200, hc34, hlam, hphi, ht0b, ht45, ht5b, p205_1, u0elo0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p205_1, u0elo0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h198, hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h196, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p205_1]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h196, hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h0, h196, hc34, hlam, hphi, ht0b, ht45, ht5b, p205_1, u0elo0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h201, hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h1, hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h197, hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h200, hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [hlam, p205_0]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h203, hlam, p205_1]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h203, hc03, hc45, hlam, hphi, ht34, p205_1]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h197, h203, hc34, hc45, hlam, hphi, p205_1]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h200, h203, hc34, hc45, hlam, hphi, p205_1]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [h203, hc34, hc45, hlam, hphi, p205_1]
                  · have p205_0 := h205c.1
                    have p205_1 := h205c.2.1
                    have p205_2 := h205c.2.2.1
                    have p205_3 := h205c.2.2.2
                    linarith only [hlam, p205_0]
            · linarith only [h1, h2, h200, hc23, hc35, hlam, hphi]
        · linarith only [h1, h197, h2, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h233 | h233
        · rcases m.htr 1 3 5 (by decide) (by decide) with h234 | h234
          · linarith only [h0, h2, h234, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
            · rcases m.htr 2 3 5 (by decide) (by decide) with h237 | h237
              · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                · linarith only [h0, h233, h238, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases h3bigk with h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h2, h237, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h2, h237, hlam, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h2, h237, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h2, hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h0, hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h196, hlam, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p240_1, u0elo0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h234, hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h1, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h196, hc12, hc23, hlam, hphi, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    rcases p240_3 (m.d 0 3) (by simp) with h254 | h254
                    · linarith only [h2, h237, h254, hlam]
                    · linarith only [h1, h254, hlam]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h2, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h1, hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h233, hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h236, hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h238, hlam, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [hc03, hc35, hlam, hphi, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h233, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h237, hlam, p240_0]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [h237, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p240_1]
                  · have p240_0 := h240c.1
                    have p240_1 := h240c.2.1
                    have p240_2 := h240c.2.2.1
                    have p240_3 := h240c.2.2.2
                    linarith only [hlam, p240_0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h268 | h268
                · linarith only [h0, h233, h268, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases h3bigk with h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u0elo2]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h196, h2, h268, hc12, hc45, hlam, hphi, ht23, ht34, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h2, h268, hc34, hc45, hlam, hphi, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h2, hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h0, hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h196, hlam, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p270_1, u0elo0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h234, hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h1, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h196, hc12, hc23, hlam, hphi, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h237, h268, hc34, hc45, hlam, hphi, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h237, hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h1, hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h233, hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h236, hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [hlam, p270_0]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h268, hlam, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h0, h233, h268, hc34, hc45, hlam, hphi, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h233, h268, hc34, hc45, hlam, hphi, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h268, hc23, hc45, hlam, hphi, ht34, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [h268, hc34, hc45, hlam, hphi, p270_1]
                  · have p270_0 := h270c.1
                    have p270_1 := h270c.2.1
                    have p270_2 := h270c.2.2.1
                    have p270_3 := h270c.2.2.2
                    linarith only [hlam, p270_0]
            · linarith only [h0, h196, h233, h236, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
        · linarith only [h1, h2, h233, hc13, hc35, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h298 | h298
    · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
      · rcases m.htr 1 3 4 (by decide) (by decide) with h300 | h300
        · linarith only [h0, h1, h300, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h302 | h302
          · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
            · linarith only [h0, h1, h299, h302, h303, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h305 | h305
              · rcases m.htr 3 4 5 (by decide) (by decide) with h306 | h306
                · rcases h3bigk with h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h299, h305, h306, hc45, hlam, hphi, ht0b, ht5b, p307_1, u0elo2]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h1, h305, h306, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h1, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h1, h306, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h0, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h305, h306, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h300, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h0, h306, hc45, hlam, hphi, ht0b, ht5b, p307_1, u0elo0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h298, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h299, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h303, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h299, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h0, h302, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h302, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hc23, hc34, hlam, hphi, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    rcases p307_3 (m.d 0 3) (by simp) with h327 | h327
                    · linarith only [h1, h327, hlam]
                    · linarith only [h298, h327, hlam]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h298, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h302, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h305, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h306, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hlam, p307_0]
                · linarith only [h0, h1, h299, h305, h306, hlam]
              · linarith only [h1, h298, h305, hc23, hc34, hlam, hphi]
          · linarith only [h1, h298, h299, h302, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h338 | h338
        · linarith only [h0, h1, h338, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h340 | h340
          · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
            · rcases m.htr 2 3 5 (by decide) (by decide) with h342 | h342
              · rcases m.htr 3 4 5 (by decide) (by decide) with h343 | h343
                · rcases h3bigk with h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h340, h343, hc45, hlam, hphi, ht0b, ht5b, p344_1, u0elo2]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h1, h341, hlam, p344_1]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h1, hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h1, h341, h343, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p344_1]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h0, hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h299, hlam, p344_1]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h338, hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h0, h343, hc45, hlam, hphi, ht0b, ht5b, p344_1, u0elo0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h298, h343, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p344_1]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h299, hc12, hc23, hlam, hphi, p344_1]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h1, h298, h343, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p344_1]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    rcases p344_3 (m.d 0 3) (by simp) with h359 | h359
                    · linarith only [h1, h341, h359, hlam]
                    · linarith only [h298, h359, hlam]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [hc03, hc34, hlam, hphi, p344_1]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h299, hc12, hc34, hlam, hphi, ht23, p344_1]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h341, hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h341, h343, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p344_1]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h298, hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h340, hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h342, hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [h343, hlam, p344_0]
                  · have p344_0 := h344c.1
                    have p344_1 := h344c.2.1
                    have p344_2 := h344c.2.2.1
                    have p344_3 := h344c.2.2.2
                    linarith only [hlam, p344_0]
                · linarith only [h0, h1, h340, h343, hlam]
              · linarith only [h0, h1, h340, h342, hc23, hc34, hlam, hphi]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h374 | h374
              · rcases m.htr 3 4 5 (by decide) (by decide) with h375 | h375
                · rcases h3bigk with h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h1, hc13, hc34, hlam, hphi, p376_1]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h1, h299, hc12, hc34, hlam, hphi, ht23, p376_1]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h1, hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h1, h375, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p376_1]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h0, hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h299, hlam, p376_1]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h338, hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h0, h375, hc45, hlam, hphi, ht0b, ht5b, p376_1, u0elo0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h298, h375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p376_1]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h299, hc12, hc23, hlam, hphi, p376_1]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h341, hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h341, h375, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p376_1]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h0, h340, h375, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p376_1]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h340, h375, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p376_1]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [hc23, hc34, hlam, hphi, p376_1]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    rcases p376_3 (m.d 0 3) (by simp) with h396 | h396
                    · linarith only [h1, h396, hlam]
                    · linarith only [h298, h396, hlam]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h298, hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h340, hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h374, hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [h375, hlam, p376_0]
                  · have p376_0 := h376c.1
                    have p376_1 := h376c.2.1
                    have p376_2 := h376c.2.2.1
                    have p376_3 := h376c.2.2.2
                    linarith only [hlam, p376_0]
                · linarith only [h299, h341, h375, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h0, h299, h340, h374, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h1, h298, h340, hc13, hc34, hlam, hphi]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h407 | h407
      · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
        · linarith only [h0, h1, h408, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h410 | h410
          · linarith only [h0, h298, h410, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
            · linarith only [h0, h1, h407, h412, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h414 | h414
              · linarith only [h0, h298, h407, h414, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
                · rcases h3bigk with h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h407, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p417_1, u0elo2]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h298, h416, hc23, hc34, hlam, hphi, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h1, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h298, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p417_1, u0elo0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h408, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h410, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h407, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h407, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h412, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h414, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, hc13, hc34, hlam, hphi, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h407, hc23, hc34, hlam, hphi, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hc23, hc34, hlam, hphi, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, h298, h407, hc23, hc34, hlam, hphi, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, h407, hc23, hc35, hlam, hphi, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h407, hc23, hc35, hlam, hphi, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hc23, hc35, hlam, hphi, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h416, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hlam, p417_0]
                · rcases h3bigk with h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h407, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p443_1, u0elo2]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h1, h416, hc23, hc45, hlam, hphi, ht34, p443_1]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h1, hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h298, hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h0, hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p443_1, u0elo0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h408, hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h410, hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h407, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p443_1]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h407, hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h412, hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h414, hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h0, h416, hc13, hc45, hlam, hphi, ht34, p443_1]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h407, h416, hc23, hc45, hlam, hphi, ht34, p443_1]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h416, hc23, hc45, hlam, hphi, ht34, p443_1]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [hlam, p443_0]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h416, hlam, p443_1]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h0, h407, h416, hc23, hc45, hlam, hphi, ht34, p443_1]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h407, h416, hc23, hc45, hlam, hphi, ht34, p443_1]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h416, hc23, hc45, hlam, hphi, ht34, p443_1]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [h1, h416, hc04, hc45, hlam, hphi, p443_1]
                  · have p443_0 := h443c.1
                    have p443_1 := h443c.2.1
                    have p443_2 := h443c.2.2.1
                    have p443_3 := h443c.2.2.2
                    linarith only [hlam, p443_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
        · linarith only [h0, h1, h469, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h471 | h471
          · linarith only [h0, h298, h471, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h473 | h473
            · rcases m.htr 2 3 5 (by decide) (by decide) with h474 | h474
              · rcases m.htr 3 4 5 (by decide) (by decide) with h475 | h475
                · rcases h3bigk with h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h407, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p476_1, u0elo2]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h298, h473, h475, hlam, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h1, hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h298, hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h0, hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h407, hlam, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h469, hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h471, hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h0, h407, hc12, hc23, hlam, hphi, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h407, hc12, hc23, hlam, hphi, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h475, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h0, h298, h407, hc12, hc23, hlam, hphi, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h0, h407, h473, hc12, hc24, hlam, hphi, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h407, h473, hc12, hc24, hlam, hphi, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h473, hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h0, h298, h407, h473, hc12, hc23, hlam, hphi, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h0, h407, h474, hc12, hc25, hlam, hphi, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h407, h474, hc12, hc25, hlam, hphi, p476_1]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h474, hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [h475, hlam, p476_0]
                  · have p476_0 := h476c.1
                    have p476_1 := h476c.2.1
                    have p476_2 := h476c.2.2.1
                    have p476_3 := h476c.2.2.2
                    linarith only [hlam, p476_0]
                · rcases h3bigk with h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h407, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p502_1, u0elo2]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h1, h298, h474, h475, hc05, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h1, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h298, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h407, hlam, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h469, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h471, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, h407, hc12, hc23, hlam, hphi, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h407, hc12, hc23, hlam, hphi, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, h1, h407, hc12, hc23, hlam, hphi, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, h1, h407, h475, hc12, hc23, hlam, hphi, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, h407, hc12, hc34, hlam, hphi, ht23, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h407, h475, hc12, hc35, hlam, hphi, ht23, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h473, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h475, hlam, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, h407, hc12, hc35, hlam, hphi, ht23, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h407, hc12, hc35, hlam, hphi, ht23, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h474, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, h1, h407, hc12, hc35, hlam, hphi, ht23, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [hlam, p502_0]
              · linarith only [h0, h1, h407, h473, h474, hc12, hc35, hlam, hphi, ht23]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h529 | h529
              · linarith only [h0, h298, h407, h473, h529, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h531 | h531
                · rcases h3bigk with h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h407, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p532_1, u0elo2]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h298, h531, hc23, hc34, hlam, hphi, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h1, hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h298, hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h0, hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h407, hlam, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h469, hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h471, hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h0, h407, h473, hc12, hc24, hlam, hphi, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h407, h473, hc12, hc24, hlam, hphi, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h473, hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h529, hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h0, h407, hc12, hc34, hlam, hphi, ht23, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h407, hc12, hc34, hlam, hphi, ht23, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [hc23, hc34, hlam, hphi, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h0, h298, h407, hc12, hc34, hlam, hphi, ht23, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h0, h407, hc12, hc35, hlam, hphi, ht23, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h407, hc12, hc35, hlam, hphi, ht23, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h407, hc12, hc35, hlam, hphi, ht23, p532_1]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [h531, hlam, p532_0]
                  · have p532_0 := h532c.1
                    have p532_1 := h532c.2.1
                    have p532_2 := h532c.2.2.1
                    have p532_3 := h532c.2.2.2
                    linarith only [hlam, p532_0]
                · linarith only [h407, h473, h531, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
