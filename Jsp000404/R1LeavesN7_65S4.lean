import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_23_L_0_H_I_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
          · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h4, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
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
                  linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10_1, u1elo0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h7, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo0]
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
                  linarith only [h7, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo2]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo0]
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
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h1, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h2, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hc13, hc34, hlam, hphi, p10_1]
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
                  linarith only [h3, hlam, p10_0]
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
                  linarith only [h0, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
            · linarith only [h0, h3, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
            · linarith only [h0, h2, h37, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · linarith only [h0, h37, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
          · linarith only [h0, h3, h4, h40, h5, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
            · linarith only [h4, h42, h5, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
              · rcases h3bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h0, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h0, h44, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p45_1, u1elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p45_1, u1elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h0, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo2]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h44, h5, hlam, p45_1]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h5, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h1, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h4, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h40, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h42, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h2, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h4, hc23, hc34, hlam, hphi, p45_1]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h0, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h0, h2, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h3, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h4, hc23, hc35, hlam, hphi, p45_1]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h0, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h44, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, p45_0]
              · rcases h3bigk with h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p71_1, u1elo0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p71_1, u1elo0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p71_1, u1elo0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p71_1, u1elo0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p71_1, u1elo2]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h40, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p71_1, u1elo2]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h5, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h1, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h4, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h40, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h42, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h2, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hc13, hc34, hlam, hphi, p71_1]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hc23, hc34, hlam, hphi, p71_1]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h44, hlam, p71_1]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h3, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p71_1, u1elo0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p71_1, u1elo0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p71_1, u1elo0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hlam, p71_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h97 | h97
        · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
          · rcases m.htr 2 3 5 (by decide) (by decide) with h99 | h99
            · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
              · rcases h3bigk with h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h0, h100, h97, hc45, hlam, hphi, ht01, ht0b, ht5b, p101_1, u1elo0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h0, h100, h98, hc45, hlam, hphi, ht01, ht0b, ht5b, p101_1, u1elo0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h0, h100, hc45, hlam, hphi, ht01, ht0b, ht5b, p101_1, u1elo0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h0, h100, hc45, hlam, hphi, ht01, ht0b, ht5b, p101_1, u1elo0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h0, hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h4, hlam, p101_1]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h100, hc45, hlam, hphi, ht01, ht0b, ht5b, p101_1, u1elo2]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h0, h100, hc45, hlam, hphi, ht01, ht0b, ht5b, p101_1, u1elo0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h1, hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h1, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h0, h1, h100, hc45, hlam, hphi, ht01, ht0b, ht5b, p101_1, u1elo0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h0, h1, h100, hc45, hlam, hphi, ht01, ht0b, ht5b, p101_1, u1elo0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h2, hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h100, h97, h98, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p101_1]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h98, hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h0, h1, h100, h98, hc45, hlam, hphi, ht01, ht0b, ht5b, p101_1, u1elo0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h3, hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h97, hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h99, hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [h100, hlam, p101_0]
                · have p101_0 := h101c.1
                  have p101_1 := h101c.2.1
                  have p101_2 := h101c.2.2.1
                  have p101_3 := h101c.2.2.2
                  linarith only [hlam, p101_0]
              · rcases h3bigk with h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h0, h100, h97, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p127_1, u1elo0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h0, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p127_1, u1elo0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h0, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p127_1, u1elo0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h0, h100, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p127_1, u1elo0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h0, hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h4, hlam, p127_1]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p127_1, u1elo2]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h100, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p127_1, u1elo2]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h1, hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h1, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p127_1]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h0, h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p127_1, u1elo0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h0, h1, h100, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p127_1, u1elo0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h2, hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h100, h97, hlam, p127_1]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h98, hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h100, hlam, p127_1]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h3, hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h97, hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h99, hlam, p127_0]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [h97, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p127_1, u1elo2]
                · have p127_0 := h127c.1
                  have p127_1 := h127c.2.1
                  have p127_2 := h127c.2.2.1
                  have p127_3 := h127c.2.2.2
                  linarith only [hlam, p127_0]
            · linarith only [h0, h97, h99, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · linarith only [h0, h2, h4, h97, h98, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
          · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
            · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
              · rcases h3bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, h155, h157, h4, h97, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, h157, h4, h97, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, h4, h97, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h4, hlam, p158_1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h157, h97, hlam, p158_1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h97, hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h1, hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h4, hc12, hc23, hlam, hphi, p158_1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, h1, h157, h4, h97, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, h1, h4, h97, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h2, hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h155, h4, hc12, hc24, hlam, hphi, p158_1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h155, hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h155, h4, h97, hc12, hc24, hlam, hphi, p158_1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h3, hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h4, hc12, hc35, hlam, hphi, ht23, p158_1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h156, hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h157, hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [hlam, p158_0]
              · rcases h3bigk with h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p184_1, u1elo0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h0, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p184_1, u1elo0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h0, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p184_1, u1elo0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h0, h157, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p184_1, u1elo0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h0, hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h4, hlam, p184_1]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p184_1, u1elo2]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h97, hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h1, hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h0, h1, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p184_1, u1elo0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h0, h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p184_1, u1elo0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h0, h1, h97, hc15, hlam, hphi, ht01, ht0b, ht5b, p184_1, u1elo0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h2, hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h4, hc12, hc34, hlam, hphi, ht23, p184_1]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h155, hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h157, hlam, p184_1]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h3, hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h4, hc12, hc35, hlam, hphi, ht23, p184_1]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h156, hlam, p184_0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [h0, h1, h156, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p184_1, u1elo0]
                · have p184_0 := h184c.1
                  have p184_1 := h184c.2.1
                  have p184_2 := h184c.2.2.1
                  have p184_3 := h184c.2.2.2
                  linarith only [hlam, p184_0]
            · linarith only [h0, h156, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · linarith only [h0, h155, h2, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h212 | h212
      · rcases m.htr 1 3 5 (by decide) (by decide) with h213 | h213
        · linarith only [h0, h213, h3, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h215 | h215
          · rcases m.htr 2 3 5 (by decide) (by decide) with h216 | h216
            · linarith only [h0, h212, h216, h3, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h218 | h218
              · linarith only [h212, h215, h218, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases h3bigk with h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h212, h215, h3, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h215, h218, h3, hc34, hc45, hlam, hphi, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h218, h3, hc34, hc45, hlam, hphi, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h3, hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h0, hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h0, h215, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h0, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p220_1, u1elo0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h213, hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h1, hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h212, hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h1, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h216, hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h2, hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [hc13, hc34, hlam, hphi, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h215, hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [hlam, p220_0]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h218, hlam, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h218, hc03, hc45, hlam, hphi, ht34, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h218, hc13, hc45, hlam, hphi, ht34, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h215, h218, hc34, hc45, hlam, hphi, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [h218, hc34, hc45, hlam, hphi, p220_1]
                · have p220_0 := h220c.1
                  have p220_1 := h220c.2.1
                  have p220_2 := h220c.2.2.1
                  have p220_3 := h220c.2.2.2
                  linarith only [hlam, p220_0]
          · linarith only [h2, h215, h3, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h247 | h247
        · linarith only [h2, h247, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
          · rcases m.htr 2 3 5 (by decide) (by decide) with h250 | h250
            · linarith only [h1, h250, h3, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
              · linarith only [h1, h249, h252, h3, hlam]
              · rcases h3bigk with h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h252, h3, hc13, hc45, hlam, hphi, ht34, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h252, h3, hc23, hc45, hlam, hphi, ht34, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h252, h3, hc34, hc45, hlam, hphi, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h3, hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h0, hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h212, hlam, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p254_1, u1elo2]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h247, hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h1, hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h1, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h1, h252, h3, hc34, hc45, hlam, hphi, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h250, hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h2, hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h212, h249, hc12, hc24, hlam, hphi, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h249, hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [hlam, p254_0]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h252, hlam, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h252, hc03, hc45, hlam, hphi, ht34, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h212, h252, hc12, hc45, hlam, hphi, ht23, ht34, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h212, h252, hc12, hc45, hlam, hphi, ht23, ht34, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [h252, hc34, hc45, hlam, hphi, p254_1]
                · have p254_0 := h254c.1
                  have p254_1 := h254c.2.1
                  have p254_2 := h254c.2.2.1
                  have p254_3 := h254c.2.2.2
                  linarith only [hlam, p254_0]
          · linarith only [h0, h2, h212, h249, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h281 | h281
    · rcases m.htr 1 2 3 (by decide) (by decide) with h282 | h282
      · rcases m.htr 1 3 5 (by decide) (by decide) with h283 | h283
        · rcases m.htr 2 3 4 (by decide) (by decide) with h284 | h284
          · linarith only [h2, h282, h284, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h286 | h286
            · rcases m.htr 3 4 5 (by decide) (by decide) with h287 | h287
              · rcases h3bigk with h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h2, hc13, hc34, hlam, hphi, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h2, h286, h287, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h2, hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h2, h287, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h0, hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h286, h287, hc45, hlam, hphi, ht01, ht0b, ht5b, p288_1, u1elo2]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h0, h2, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p288_1, u1elo0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h287, hc45, hlam, hphi, ht01, ht0b, ht5b, p288_1, u1elo2]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h1, hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h282, hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h284, hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h1, h287, hc02, hc45, hlam, hphi, ht0b, ht5b, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hc03, hc34, hlam, hphi, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hc13, hc34, hlam, hphi, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hc23, hc34, hlam, hphi, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  rcases p288_3 (m.d 0 3) (by simp) with h308 | h308
                  · linarith only [h2, h308, hlam]
                  · linarith only [h281, h308, hlam]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h281, hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h283, hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h286, hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h287, hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hlam, p288_0]
              · linarith only [h0, h2, h282, h286, h287, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h2, h283, h286, hc23, hc34, hlam, hphi]
        · linarith only [h2, h281, h283, hc13, hc34, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h319 | h319
        · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
          · linarith only [h0, h1, h2, h319, h320, hc02, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
            · rcases m.htr 3 4 5 (by decide) (by decide) with h323 | h323
              · rcases h3bigk with h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h319, h323, hc03, hc45, hlam, hphi, ht0b, ht5b, p324_1]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h2, h282, hc12, hc34, hlam, hphi, ht23, p324_1]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h2, hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h2, h323, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p324_1]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h0, hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h282, hlam, p324_1]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h2, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p324_1, u1elo2]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h323, hc45, hlam, hphi, ht01, ht0b, ht5b, p324_1, u1elo2]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h1, hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h1, h2, hc13, hc34, hlam, hphi, p324_1]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h320, hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h1, h2, h323, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p324_1]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [hc03, hc34, hlam, hphi, p324_1]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h319, h323, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p324_1]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h282, hc12, hc34, hlam, hphi, ht23, p324_1]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  rcases p324_3 (m.d 0 3) (by simp) with h344 | h344
                  · linarith only [h2, h344, hlam]
                  · linarith only [h281, h344, hlam]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h281, hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h319, hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h322, hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [h323, hlam, p324_0]
                · have p324_0 := h324c.1
                  have p324_1 := h324c.2.1
                  have p324_2 := h324c.2.2.1
                  have p324_3 := h324c.2.2.2
                  linarith only [hlam, p324_0]
              · linarith only [h1, h2, h282, h323, hc12, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h282, h319, h322, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
        · linarith only [h2, h281, h319, hc13, hc34, hlam, hphi]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h355 | h355
      · rcases m.htr 1 3 5 (by decide) (by decide) with h356 | h356
        · linarith only [h0, h281, h356, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h358 | h358
          · linarith only [h0, h2, h355, h358, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h360 | h360
            · linarith only [h0, h281, h355, h360, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h362 | h362
              · rcases h3bigk with h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [hlam, p363_0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h281, h355, h362, hc23, hc34, hlam, hphi, p363_1]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h281, h362, hc23, hc34, hlam, hphi, p363_1]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h2, hlam, p363_0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h281, hlam, p363_0]
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
                  linarith only [hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p363_1, u1elo2]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h0, h281, h362, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p363_1, u1elo0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h356, hlam, p363_0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h1, hlam, p363_0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h355, hlam, p363_0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [hlam, p363_0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h358, hlam, p363_0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h360, hlam, p363_0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h0, hc13, hc34, hlam, hphi, p363_1]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h355, hc23, hc34, hlam, hphi, p363_1]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [hc23, hc34, hlam, hphi, p363_1]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [hlam, p363_0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h0, h281, h355, hc23, hc34, hlam, hphi, p363_1]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h0, h355, hc23, hc35, hlam, hphi, p363_1]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h355, hc23, hc35, hlam, hphi, p363_1]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [hc23, hc35, hlam, hphi, p363_1]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [h362, hlam, p363_0]
                · have p363_0 := h363c.1
                  have p363_1 := h363c.2.1
                  have p363_2 := h363c.2.2.1
                  have p363_3 := h363c.2.2.2
                  linarith only [hlam, p363_0]
              · rcases h3bigk with h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h0, h355, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p389_1, u1elo0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h0, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p389_1, u1elo0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h2, hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h281, hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h0, hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p389_1, u1elo2]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h0, h2, hlam, p389_1]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h356, hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h1, hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h355, hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h358, hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h360, hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h362, hc03, hc45, hlam, hphi, ht34, p389_1]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h355, h362, hc23, hc45, hlam, hphi, ht34, p389_1]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h362, hc23, hc45, hlam, hphi, ht34, p389_1]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [hlam, p389_0]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h362, hlam, p389_1]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h0, h355, h362, hc23, hc45, hlam, hphi, ht34, p389_1]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h355, h362, hc23, hc45, hlam, hphi, ht34, p389_1]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h362, hc23, hc45, hlam, hphi, ht34, p389_1]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [h2, h362, hc04, hc45, hlam, hphi, p389_1]
                · have p389_0 := h389c.1
                  have p389_1 := h389c.2.1
                  have p389_2 := h389c.2.2.1
                  have p389_3 := h389c.2.2.2
                  linarith only [hlam, p389_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h415 | h415
        · linarith only [h1, h281, h355, h415, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h417 | h417
          · linarith only [h1, h2, h417, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h419 | h419
            · linarith only [h1, h281, h419, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h421 | h421
              · rcases h3bigk with h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h281, h421, hc13, hc34, hlam, hphi, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h281, h355, h421, hc12, hc34, hlam, hphi, ht23, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h2, hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h281, hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h0, hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h355, hlam, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h281, h421, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p422_1, u1elo2]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h415, hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h1, hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h1, h281, h421, hc13, hc34, hlam, hphi, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h417, hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h419, hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [hc03, hc34, hlam, hphi, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h355, hc12, hc34, hlam, hphi, ht23, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h355, hc12, hc34, hlam, hphi, ht23, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h1, h281, h355, hc12, hc34, hlam, hphi, ht23, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h1, h355, hc12, hc35, hlam, hphi, ht23, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h355, hc12, hc35, hlam, hphi, ht23, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h355, hc12, hc35, hlam, hphi, ht23, p422_1]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [h421, hlam, p422_0]
                · have p422_0 := h422c.1
                  have p422_1 := h422c.2.1
                  have p422_2 := h422c.2.2.1
                  have p422_3 := h422c.2.2.2
                  linarith only [hlam, p422_0]
              · linarith only [h1, h2, h355, h421, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
