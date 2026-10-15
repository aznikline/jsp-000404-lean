import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1741 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h2261 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2601 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h2602 | h2602
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2603 | h2603
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2604 | h2604
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2605 | h2605
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2606 | h2606
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2607 | h2607
            · rcases h5bigk with h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [hlam, p2608_0]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h0, hlam, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h1741, hlam, p2608_0]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2261, h2607, hlam, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2261, hlam, p2608_0]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2608_1, u1elo4]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [hlam, p2608_0]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2261, h2601, h2605, h2607, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2608_1, u1elo1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2261, h2601, h2607, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2608_1, u1elo1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2261, h2601, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2608_1, u1elo1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2601, hlam, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [hlam, p2608_0]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2261, h2601, h2607, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2608_1, u1elo1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2261, h2601, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2608_1, u1elo1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2602, hlam, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2605, hlam, p2608_0]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [hlam, p2608_0]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2261, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h0, h2604, h2607, hc01, hc23, hlam, hphi, ht12, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2603, hlam, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2606, hlam, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [h2607, hlam, p2608_1]
              · have p2608_0 := h2608c.1
                have p2608_1 := h2608c.2.1
                have p2608_2 := h2608c.2.2.1
                have p2608_3 := h2608c.2.2.2
                linarith only [hlam, p2608_0]
            · rcases h5bigk with h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [hlam, p2634_0]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h0, hlam, p2634_1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h1741, hlam, p2634_0]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h0, h2601, hc35, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u1elo1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2261, hlam, p2634_0]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2601, hc05, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u1elo1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [hlam, p2634_0]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h1741, h2601, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2634_1, u1elo1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2601, hc35, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u1elo1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2601, h2607, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2634_1, u1elo1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2634_1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2601, hlam, p2634_1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [hlam, p2634_0]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2601, hc35, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u1elo1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2601, h2607, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2634_1, u1elo1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2634_1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2602, hlam, p2634_1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2605, hlam, p2634_0]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [hlam, p2634_0]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2607, hlam, p2634_0]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h0, h2606, hc01, hc24, hlam, hphi, ht12, p2634_1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2603, hlam, p2634_1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2606, hlam, p2634_1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [h2601, h2606, hc35, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u1elo1]
              · have p2634_0 := h2634c.1
                have p2634_1 := h2634c.2.1
                have p2634_2 := h2634c.2.2.1
                have p2634_3 := h2634c.2.2.2
                linarith only [hlam, p2634_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2660 | h2660
            · linarith only [h1741, h2604, h2606, h2660, hc02, hc23, hlam, hphi]
            · rcases h5bigk with h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [hlam, p2662_0]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h0, hlam, p2662_1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h1741, hlam, p2662_0]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h0, h2601, h2660, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2662_1, u1elo1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2261, hlam, p2662_0]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2601, hc05, hlam, hphi, ht01, ht0b, ht5b, p2662_1, u1elo1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [hlam, p2662_0]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h1741, h2601, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2662_1, u1elo1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2601, h2660, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2662_1, u1elo1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2601, h2606, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2662_1, u1elo1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2662_1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2601, hlam, p2662_1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [hlam, p2662_0]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2601, h2660, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2662_1, u1elo1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2606, hlam, p2662_0]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h0, h1741, h2603, h2606, hc01, hc02, hc35, hlam, hphi, ht23, p2662_1, u1elo3]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2602, hlam, p2662_1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2605, hlam, p2662_0]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [hlam, p2662_0]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2660, hlam, p2662_0]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h0, h2603, hc01, hlam, hphi, p2662_1, u1elo3]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2603, hlam, p2662_1]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h1741, h2603, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2662_1, u1elo3]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [h2603, hc35, hlam, hphi, ht01, ht0b, ht5b, p2662_1, u1elo3]
              · have p2662_0 := h2662c.1
                have p2662_1 := h2662c.2.1
                have p2662_2 := h2662c.2.2.1
                have p2662_3 := h2662c.2.2.2
                linarith only [hlam, p2662_0]
        · linarith only [h2602, h2604, h2605, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2689 | h2689
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2690 | h2690
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2691 | h2691
            · rcases h5bigk with h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [hlam, p2692_0]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h0, hlam, p2692_1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h1741, hlam, p2692_0]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h0, h2601, hc35, hlam, hphi, ht01, ht0b, ht5b, p2692_1, u1elo1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2261, hlam, p2692_0]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2601, hc05, hlam, hphi, ht01, ht0b, ht5b, p2692_1, u1elo1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [hlam, p2692_0]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h1741, h2261, h2601, h2604, h2689, h2691, hc02, hc04, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, p2692_1, u1elo1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2261, h2601, h2691, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2692_1, u1elo1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2261, h2601, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2692_1, u1elo1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2692_1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2601, hlam, p2692_1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [hlam, p2692_0]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2261, h2601, h2691, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2692_1, u1elo1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2261, h2601, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2692_1, u1elo1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h0, h2604, h2689, hc01, hc34, hlam, hphi, ht12, ht23, p2692_1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2602, hlam, p2692_1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2689, hlam, p2692_0]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [hlam, p2692_0]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2261, h2604, h2689, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2692_1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2692_1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2603, hlam, p2692_1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2690, hlam, p2692_1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [h2691, hlam, p2692_1]
              · have p2692_0 := h2692c.1
                have p2692_1 := h2692c.2.1
                have p2692_2 := h2692c.2.2.1
                have p2692_3 := h2692c.2.2.2
                linarith only [hlam, p2692_0]
            · linarith only [h2601, h2604, h2690, h2691, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
          · linarith only [h1741, h2603, h2604, h2689, h2690, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2720 | h2720
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2721 | h2721
            · rcases h5bigk with h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c | h2722c
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [hlam, p2722_0]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h0, hlam, p2722_1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h1741, hlam, p2722_0]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2689, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2722_1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2261, hlam, p2722_0]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2601, hc05, hlam, hphi, ht01, ht0b, ht5b, p2722_1, u1elo1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [hlam, p2722_0]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h1741, h2601, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2722_1, u1elo1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2601, h2689, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2722_1, u1elo1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2601, hc45, hlam, hphi, ht01, ht0b, ht5b, p2722_1, u1elo1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2722_1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2601, hlam, p2722_1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [hlam, p2722_0]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2689, hlam, p2722_1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2261, h2602, h2689, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2722_1, u1elo2]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h0, h2602, hc01, hlam, hphi, p2722_1, u1elo2]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2602, hlam, p2722_1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h1741, h2602, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2722_1, u1elo2]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [hlam, p2722_0]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2261, h2602, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2722_1, u1elo2]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h0, h2720, hc01, hc24, hlam, hphi, ht12, p2722_1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2603, hlam, p2722_1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2720, hlam, p2722_1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [h2721, hlam, p2722_1]
              · have p2722_0 := h2722c.1
                have p2722_1 := h2722c.2.1
                have p2722_2 := h2722c.2.2.1
                have p2722_3 := h2722c.2.2.2
                linarith only [hlam, p2722_0]
            · linarith only [h2602, h2604, h2689, h2720, h2721, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2749 | h2749
            · rcases h5bigk with h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [hlam, p2750_0]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h0, hlam, p2750_1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h1741, hlam, p2750_0]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h1741, h2720, h2749, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2750_1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h2261, hlam, p2750_0]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h2601, hc05, hlam, hphi, ht01, ht0b, ht5b, p2750_1, u1elo1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [hlam, p2750_0]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h1741, h2601, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2750_1, u1elo1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h1741, h2601, h2720, h2749, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2750_1, u1elo1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h1741, h2601, h2720, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2750_1, u1elo1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2750_1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h2601, hlam, p2750_1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [hlam, p2750_0]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h2689, hlam, p2750_1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h2720, hlam, p2750_0]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h0, h2602, hc01, hlam, hphi, p2750_1, u1elo2]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h2602, hlam, p2750_1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h1741, h2602, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2750_1, u1elo2]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [hlam, p2750_0]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h1741, h2602, h2720, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2750_1, u1elo2]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2750_1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h2603, hlam, p2750_1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h1741, h2603, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2750_1, u1elo3]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [h2749, hlam, p2750_1]
              · have p2750_0 := h2750c.1
                have p2750_1 := h2750c.2.1
                have p2750_2 := h2750c.2.2.1
                have p2750_3 := h2750c.2.2.2
                linarith only [hlam, p2750_0]
            · linarith only [h2603, h2604, h2749, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2777 | h2777
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2778 | h2778
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2779 | h2779
          · linarith only [h0, h2601, h2603, h2779, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2781 | h2781
            · linarith only [h0, h2603, h2777, h2781, hc01, hc23, hlam, hphi, ht12]
            · rcases h5bigk with h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c | h2783c
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [hlam, p2783_0]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h0, hlam, p2783_1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h1741, hlam, p2783_0]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p2783_1, u1elo4]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2261, hlam, p2783_0]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2783_1, u1elo4]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [hlam, p2783_0]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2601, hc25, hlam, hphi, ht01, ht0b, ht5b, p2783_1, u1elo1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2601, hc35, hlam, hphi, ht01, ht0b, ht5b, p2783_1, u1elo1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2603, hlam, p2783_0]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2783_1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2601, hlam, p2783_1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [hlam, p2783_0]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2601, hc35, hlam, hphi, ht01, ht0b, ht5b, p2783_1, u1elo1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2779, hlam, p2783_0]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2783_1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2602, hlam, p2783_1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2778, hlam, p2783_0]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [hlam, p2783_0]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2781, hlam, p2783_0]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2783_1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2783_1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2779, hc24, hc45, hlam, hphi, p2783_1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [h2781, hc34, hc45, hlam, hphi, p2783_1]
              · have p2783_0 := h2783c.1
                have p2783_1 := h2783c.2.1
                have p2783_2 := h2783c.2.2.1
                have p2783_3 := h2783c.2.2.2
                linarith only [hlam, p2783_0]
        · linarith only [h2602, h2777, h2778, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2810 | h2810
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2811 | h2811
          · linarith only [h0, h2601, h2603, h2811, hc01, hlam, hphi, u1elo1]
          · linarith only [h2777, h2810, h2811, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2814 | h2814
          · linarith only [h0, h2601, h2603, h2814, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2816 | h2816
            · linarith only [h0, h2602, h2603, h2816, hc01, hlam, hphi, u1elo2]
            · rcases h5bigk with h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [hlam, p2818_0]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h0, hlam, p2818_1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h1741, hlam, p2818_0]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h0, h2810, hc25, hlam, hphi, ht01, ht0b, ht5b, p2818_1, u1elo4]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h2261, hlam, p2818_0]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2818_1, u1elo4]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [hlam, p2818_0]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h1741, h2601, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2818_1, u1elo1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h1741, h2601, h2810, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2818_1, u1elo1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h2603, hlam, p2818_0]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2818_1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h2601, hlam, p2818_1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [hlam, p2818_0]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h2810, hlam, p2818_1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h2814, hlam, p2818_0]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h0, h2602, hc01, hlam, hphi, p2818_1, u1elo2]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h2602, hlam, p2818_1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h1741, h2602, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2818_1, u1elo2]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [hlam, p2818_0]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h2816, hlam, p2818_0]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2818_1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2818_1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h1741, hc02, hc45, hlam, hphi, ht23, ht34, p2818_1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [h1741, h2810, hc02, hc45, hlam, hphi, ht23, ht34, p2818_1]
              · have p2818_0 := h2818c.1
                have p2818_1 := h2818c.2.1
                have p2818_2 := h2818c.2.2.1
                have p2818_3 := h2818c.2.2.2
                linarith only [hlam, p2818_0]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2844 | h2844
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2845 | h2845
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2846 | h2846
        · linarith only [h0, h2601, h2602, h2846, hc01, hlam, hphi, u1elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2848 | h2848
          · linarith only [h2261, h2601, h2845, h2846, h2848, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2850 | h2850
            · linarith only [h2845, h2846, h2848, h2850, hlam]
            · linarith only [h2844, h2845, h2846, h2850, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2853 | h2853
        · linarith only [h0, h2602, h2845, h2853, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2855 | h2855
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2856 | h2856
            · rcases h5bigk with h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [hlam, p2857_0]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h0, hlam, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h1741, hlam, p2857_0]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h0, h2602, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2261, hlam, p2857_0]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2857_1, u1elo4]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [hlam, p2857_0]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2601, hc25, hlam, hphi, ht01, ht0b, ht5b, p2857_1, u1elo1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2602, hlam, p2857_0]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2261, h2601, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2857_1, u1elo1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2601, hlam, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [hlam, p2857_0]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2853, hlam, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2261, h2601, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2857_1, u1elo1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2853, hc23, hc35, hlam, hphi, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [hlam, p2857_0]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2261, h2856, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h0, h2855, hc01, hc24, hlam, hphi, ht12, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2844, hlam, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2855, hlam, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [h2856, hlam, p2857_1]
              · have p2857_0 := h2857c.1
                have p2857_1 := h2857c.2.1
                have p2857_2 := h2857c.2.2.1
                have p2857_3 := h2857c.2.2.2
                linarith only [hlam, p2857_0]
            · linarith only [h2601, h2845, h2855, h2856, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2884 | h2884
            · rcases h5bigk with h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [hlam, p2885_0]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h0, hlam, p2885_1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h1741, hlam, p2885_0]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p2885_1, u1elo4]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h2261, hlam, p2885_0]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2885_1, u1elo4]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [hlam, p2885_0]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h1741, h2601, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2885_1, u1elo1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h2602, hlam, p2885_0]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h2601, h2855, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2885_1, u1elo1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2885_1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h2601, hlam, p2885_1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [hlam, p2885_0]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h2853, hlam, p2885_1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h2855, hlam, p2885_0]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h0, h2884, hc01, hc34, hlam, hphi, ht12, ht23, p2885_1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h0, h2884, hc01, hc34, hlam, hphi, ht12, ht23, p2885_1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h1741, h2884, hc02, hc34, hlam, hphi, ht23, p2885_1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [hlam, p2885_0]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h1741, h2855, h2884, hc02, hc34, hlam, hphi, ht23, p2885_1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h0, h2844, hc01, hlam, hphi, p2885_1, u1elo3]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h2844, hlam, p2885_1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h1741, h2844, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2885_1, u1elo3]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [h2884, hlam, p2885_1]
              · have p2885_0 := h2885c.1
                have p2885_1 := h2885c.2.1
                have p2885_2 := h2885c.2.2.1
                have p2885_3 := h2885c.2.2.2
                linarith only [hlam, p2885_0]
            · linarith only [h2844, h2845, h2884, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2912 | h2912
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2913 | h2913
        · linarith only [h0, h2601, h2602, h2913, hc01, hlam, hphi, u1elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2915 | h2915
          · linarith only [h0, h2844, h2912, h2913, h2915, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2917 | h2917
            · linarith only [h0, h2601, h2844, h2912, h2913, h2917, hc01, hlam, hphi, u1elo1]
            · rcases h5bigk with h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [hlam, p2919_0]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h0, hlam, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h1741, hlam, p2919_0]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h2912, h2913, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h2261, hlam, p2919_0]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2919_1, u1elo4]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [hlam, p2919_0]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h2601, hc25, hlam, hphi, ht01, ht0b, ht5b, p2919_1, u1elo1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h2602, hlam, p2919_0]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h2844, hlam, p2919_0]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h2601, hlam, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [hlam, p2919_0]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h2913, hlam, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h2915, hlam, p2919_0]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h0, h2917, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h1741, h2917, hc02, hc45, hlam, hphi, ht23, ht34, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [hlam, p2919_0]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h2917, hlam, p2919_0]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h1741, hc02, hc45, hlam, hphi, ht23, ht34, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [h2602, hc13, hc45, hlam, hphi, ht34, p2919_1]
              · have p2919_0 := h2919c.1
                have p2919_1 := h2919c.2.1
                have p2919_2 := h2919c.2.2.1
                have p2919_3 := h2919c.2.2.2
                linarith only [hlam, p2919_0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2945 | h2945
        · linarith only [h0, h2602, h2912, h2945, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2947 | h2947
          · linarith only [h0, h2601, h2844, h2947, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2949 | h2949
            · rcases h5bigk with h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [hlam, p2950_0]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h0, hlam, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h1741, hlam, p2950_0]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h0, h2844, h2949, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h2261, hlam, p2950_0]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2950_1, u1elo4]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [hlam, p2950_0]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h2601, hc25, hlam, hphi, ht01, ht0b, ht5b, p2950_1, u1elo1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h2602, hlam, p2950_0]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h2844, hlam, p2950_0]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h2601, hlam, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [hlam, p2950_0]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h2945, hlam, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h2947, hlam, p2950_0]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h1741, hc02, hc35, hlam, hphi, ht23, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [hlam, p2950_0]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h2912, h2947, h2949, hc23, hc34, hlam, hphi, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h1741, hc02, hc45, hlam, hphi, ht23, ht34, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [h2949, hlam, p2950_1]
              · have p2950_0 := h2950c.1
                have p2950_1 := h2950c.2.1
                have p2950_2 := h2950c.2.2.1
                have p2950_3 := h2950c.2.2.2
                linarith only [hlam, p2950_0]
            · rcases h5bigk with h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [hlam, p2976_0]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h0, hlam, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h1741, hlam, p2976_0]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p2976_1, u1elo4]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h2261, hlam, p2976_0]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2976_1, u1elo4]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [hlam, p2976_0]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h1741, h2601, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2976_1, u1elo1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h2602, hlam, p2976_0]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h2844, hlam, p2976_0]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h2601, hlam, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [hlam, p2976_0]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h2945, hlam, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h2947, hlam, p2976_0]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h1741, hc02, hc35, hlam, hphi, ht23, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [hlam, p2976_0]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h2949, hlam, p2976_0]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h1741, hc02, hc45, hlam, hphi, ht23, ht34, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [h2602, hc13, hc45, hlam, hphi, ht34, p2976_1]
              · have p2976_0 := h2976c.1
                have p2976_1 := h2976c.2.1
                have p2976_2 := h2976c.2.2.1
                have p2976_3 := h2976c.2.2.2
                linarith only [hlam, p2976_0]

end R2N4
