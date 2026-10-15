import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4024000 in
set_option maxHeartbeats 4024000 in
theorem r1l7_14_25_L_0_H_I_x0_x0_x0 (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
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
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p14_1, u4elo0]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p14_1, u4elo0]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p14_1, u4elo0]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p14_1, u4elo0]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h1, hlam, p14_0]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [hlam, p14_0]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h1, hc01, hc25, hlam, hphi, ht0b, ht5b, p14_1]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h1, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p14_1, u4elo0]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p14_1, u4elo0]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h2, hlam, p14_1]
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
                          linarith only [h2, hc02, hc35, hlam, hphi, ht0b, ht5b, p14_1]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h1, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p14_1, u4elo0]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h3, hlam, p14_1]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h8, hlam, p14_1]
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
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p14_1]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h4, hlam, p14_1]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h9, hlam, p14_1]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h12, hlam, p14_1]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [h13, hlam, p14_1]
                        · have p14_0 := h14c.1
                          have p14_1 := h14c.2.1
                          have p14_2 := h14c.2.2.1
                          have p14_3 := h14c.2.2.2
                          linarith only [hlam, p14_0]
                      · linarith only [h13, h4, hc34, hlam, hphi, u4elo0]
                    · linarith only [h0, h12, h9, hc24, hlam, hphi, u4elo0]
                  · linarith only [h1, h10, h11, h4, h8, hc34, hlam, hphi, u4elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                      · rcases h5bigk with h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [hlam, p46_0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p46_1, u4elo0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p46_1, u4elo0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h4, h45, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p46_1, u4elo0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p46_1, u4elo0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h1, hlam, p46_0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [hlam, p46_0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h1, hc01, hc25, hlam, hphi, ht0b, ht5b, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h1, h4, h45, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p46_1, u4elo0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p46_1, u4elo0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h2, hlam, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h6, hlam, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [hlam, p46_0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h2, h45, hc02, hc45, hlam, hphi, ht0b, ht5b, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h0, h10, h43, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p46_1, u4elo0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h3, hlam, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h8, hlam, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h43, hlam, p46_0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [hlam, p46_0]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h4, hlam, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h9, hlam, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h44, hlam, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [h45, hlam, p46_1]
                        · have p46_0 := h46c.1
                          have p46_1 := h46c.2.1
                          have p46_2 := h46c.2.2.1
                          have p46_3 := h46c.2.2.2
                          linarith only [hlam, p46_0]
                      · linarith only [h10, h45, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h44, h9, hc24, hlam, hphi, u4elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                      · rcases h5bigk with h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [hlam, p76_0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p76_1, u4elo0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h4, h43, hc23, hlam, hphi, ht34, p76_1, u4elo0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h4, h43, hc23, hlam, hphi, ht34, p76_1, u4elo0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p76_1, u4elo0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h1, hlam, p76_0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [hlam, p76_0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h1, h43, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h1, h4, h43, hc23, hlam, hphi, ht34, p76_1, u4elo0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p76_1, u4elo0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h2, hlam, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h6, hlam, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [hlam, p76_0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h43, hlam, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h3, hlam, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h8, hlam, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h3, hc03, hc25, hlam, hphi, ht0b, ht5b, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [hlam, p76_0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h1, h4, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p76_1, u4elo0]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h4, hlam, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h9, hlam, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h74, hlam, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [h75, hlam, p76_1]
                        · have p76_0 := h76c.1
                          have p76_1 := h76c.2.1
                          have p76_2 := h76c.2.2.1
                          have p76_3 := h76c.2.2.2
                          linarith only [hlam, p76_0]
                      · linarith only [h10, h4, h75, hc24, hlam, hphi, u4elo0]
                    · linarith only [h0, h10, h74, h9, hc23, hlam, hphi, ht34, u4elo0]
              · linarith only [h4, h9, hc14, hlam, hphi, u4elo0]
            · linarith only [h3, h4, h7, h8, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h106 | h106
            · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
              · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                · linarith only [h106, h108, h5, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h111 | h111
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                      · rcases h5bigk with h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [hlam, p113_0]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p113_1, u4elo0]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p113_1, u4elo0]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h112, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p113_1, u4elo0]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p113_1, u4elo0]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h1, hlam, p113_0]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [hlam, p113_0]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h1, hc01, hc25, hlam, hphi, ht0b, ht5b, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h106, h112, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h106, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p113_1, u4elo3]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h2, hlam, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h6, hlam, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [hlam, p113_0]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h112, h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h108, h110, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p113_1, u4elo2]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h3, hlam, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h106, hlam, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h110, hlam, p113_0]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [hlam, p113_0]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h4, hlam, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h107, hlam, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h111, hlam, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [h112, hlam, p113_1]
                        · have p113_0 := h113c.1
                          have p113_1 := h113c.2.1
                          have p113_2 := h113c.2.2.1
                          have p113_3 := h113c.2.2.2
                          linarith only [hlam, p113_0]
                      · linarith only [h112, h7, hc13, hlam, hphi, ht34, u4elo4]
                    · linarith only [h106, h107, h111, h7, hc24, hlam, hphi, u4elo3]
                  · linarith only [h106, h110, h7, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h107, h4, hc14, hlam, hphi, u4elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
              · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                · linarith only [h106, h144, h3, h4, h5, hc34, hlam, hphi, u4elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                  · linarith only [h106, h146, h5, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h148 | h148
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h149 | h149
                      · rcases h5bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [hlam, p150_0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p150_1, u4elo0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h146, h4, hc23, hlam, hphi, ht34, p150_1, u4elo0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h106, h4, hc13, hlam, hphi, ht34, p150_1, u4elo0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p150_1, u4elo0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h1, hlam, p150_0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [hlam, p150_0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h1, h146, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h106, hlam, p150_0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h143, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p150_1, u4elo1]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h2, hlam, p150_1]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h6, hlam, p150_1]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [hlam, p150_0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h146, hlam, p150_1]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h148, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p150_1, u4elo2]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h3, hlam, p150_1]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p150_1, u4elo0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h3, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p150_1, u4elo0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [hlam, p150_0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h3, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p150_1, u4elo0]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h4, hlam, p150_1]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h143, hlam, p150_1]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h148, hlam, p150_1]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [h149, hlam, p150_1]
                        · have p150_0 := h150c.1
                          have p150_1 := h150c.2.1
                          have p150_2 := h150c.2.2.1
                          have p150_3 := h150c.2.2.2
                          linarith only [hlam, p150_0]
                      · linarith only [h144, h149, h4, hc24, hlam, hphi, u4elo0]
                    · linarith only [h143, h148, hc24, hlam, hphi, u4elo1]
              · linarith only [h143, h4, hc14, hlam, hphi, u4elo0]
        · linarith only [h2, h4, h5, h6, hc23, hlam, hphi, ht34, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h180 | h180
        · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
          · rcases m.htr 1 3 5 (by decide) (by decide) with h182 | h182
            · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
              · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                      · rcases h5bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p188_1, u4elo0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h185, h187, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p188_1, u4elo0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h187, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p188_1, u4elo0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p188_1, u4elo0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h1, hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h1, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h180, h187, h5, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h183, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p188_1, u4elo1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h2, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h180, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h187, h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h180, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h3, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h182, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h185, hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h4, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h183, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h186, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h187, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [hlam, p188_0]
                      · linarith only [h187, h4, hc34, hlam, hphi, u4elo0]
                    · linarith only [h0, h183, h186, hc24, hlam, hphi, u4elo0]
                  · linarith only [h180, h185, h3, h5, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h184, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h183, h4, hc14, hlam, hphi, u4elo0]
            · linarith only [h181, h182, h3, h4, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
            · rcases m.htr 1 4 5 (by decide) (by decide) with h221 | h221
              · rcases m.htr 2 3 4 (by decide) (by decide) with h222 | h222
                · rcases m.htr 2 3 5 (by decide) (by decide) with h223 | h223
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h224 | h224
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h225 | h225
                      · rcases h5bigk with h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p226_1, u4elo0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h223, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p226_1, u4elo0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p226_1, u4elo0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p226_1, u4elo0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h1, hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h1, h223, hc01, hc35, hlam, hphi, ht0b, ht5b, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h180, h181, h222, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p226_1, u4elo2]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h180, h181, h222, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p226_1, u4elo2]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h2, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h180, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h2, hc02, hc35, hlam, hphi, ht0b, ht5b, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h180, h181, h222, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p226_1, u4elo2]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h3, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h220, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h223, hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h4, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h221, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h224, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h225, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [hlam, p226_0]
                      · linarith only [h181, h225, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h180, h181, h222, h223, h224, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                  · linarith only [h180, h181, h222, h223, h5, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h180, h222, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
              · linarith only [h221, h4, hc14, hlam, hphi, u4elo0]
            · linarith only [h180, h220, h5, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h258 | h258
          · rcases m.htr 1 3 5 (by decide) (by decide) with h259 | h259
            · rcases m.htr 1 4 5 (by decide) (by decide) with h260 | h260
              · rcases m.htr 2 3 4 (by decide) (by decide) with h261 | h261
                · rcases m.htr 2 3 5 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h263 | h263
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h264 | h264
                      · rcases h5bigk with h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [hlam, p265_0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h180, h4, hc12, hlam, hphi, ht23, ht34, p265_1, u4elo0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h180, h4, hc12, hlam, hphi, ht23, ht34, p265_1, u4elo0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p265_1, u4elo0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p265_1, u4elo0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h1, hlam, p265_0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [hlam, p265_0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h180, hlam, p265_0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p265_1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h260, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p265_1, u4elo1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h2, hlam, p265_1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h263, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p265_1, u4elo2]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [hlam, p265_0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h2, hc02, hc35, hlam, hphi, ht0b, ht5b, p265_1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p265_1, u4elo0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h3, hlam, p265_1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h259, hlam, p265_1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h262, hlam, p265_0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [hlam, p265_0]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p265_1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h4, hlam, p265_1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h260, hlam, p265_1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h263, hlam, p265_1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [h264, hlam, p265_1]
                        · have p265_0 := h265c.1
                          have p265_1 := h265c.2.1
                          have p265_2 := h265c.2.2.1
                          have p265_3 := h265c.2.2.2
                          linarith only [hlam, p265_0]
                      · linarith only [h264, h4, hc34, hlam, hphi, u4elo0]
                    · linarith only [h260, h263, hc24, hlam, hphi, u4elo1]
                  · linarith only [h259, h262, h5, hlam]
                · linarith only [h261, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h260, h4, hc14, hlam, hphi, u4elo0]
            · linarith only [h258, h259, h3, h4, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h297 | h297
            · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
              · rcases m.htr 2 3 4 (by decide) (by decide) with h299 | h299
                · rcases m.htr 2 3 5 (by decide) (by decide) with h300 | h300
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h301 | h301
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h302 | h302
                      · rcases h5bigk with h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [hlam, p303_0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p303_1, u4elo0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p303_1, u4elo0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h302, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p303_1, u4elo0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p303_1, u4elo0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h1, hlam, p303_0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [hlam, p303_0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h180, hlam, p303_0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h1, h302, hc01, hc45, hlam, hphi, ht0b, ht5b, p303_1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h258, h297, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p303_1, u4elo1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h2, hlam, p303_1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p303_1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [hlam, p303_0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h2, h302, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p303_1, u4elo0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p303_1, u4elo0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h3, hlam, p303_1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h297, hlam, p303_1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h300, hlam, p303_0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [hlam, p303_0]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p303_1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h4, hlam, p303_1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h298, hlam, p303_1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h301, hlam, p303_1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [h302, hlam, p303_1]
                        · have p303_0 := h303c.1
                          have p303_1 := h303c.2.1
                          have p303_2 := h303c.2.2.1
                          have p303_3 := h303c.2.2.2
                          linarith only [hlam, p303_0]
                      · linarith only [h258, h302, hc13, hlam, hphi, ht34, u4elo4]
                    · linarith only [h301, h4, hc24, hlam, hphi, u4elo0]
                  · linarith only [h258, h297, h299, h300, hlam]
                · linarith only [h299, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h298, h4, hc14, hlam, hphi, u4elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h334 | h334
              · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h338 | h338
                      · rcases h5bigk with h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [hlam, p339_0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h297, h4, hc13, hlam, hphi, ht34, p339_1, u4elo0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p339_1, u4elo0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h297, h4, hc13, hlam, hphi, ht34, p339_1, u4elo0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p339_1, u4elo0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h1, hlam, p339_0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [hlam, p339_0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h180, hlam, p339_0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h297, hlam, p339_0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p339_1]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h2, hlam, p339_1]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p339_1]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [hlam, p339_0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h2, h297, h4, h5, hc12, hlam, hphi, ht23, ht34, p339_1, u4elo0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p339_1, u4elo0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h3, hlam, p339_1]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h297, h5, hc12, hc35, hlam, hphi, ht23, p339_1]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h336, hlam, p339_0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [hlam, p339_0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h2, h336, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p339_1, u4elo0]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h4, hlam, p339_1]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h334, hlam, p339_1]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h337, hlam, p339_1]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [h338, hlam, p339_1]
                        · have p339_0 := h339c.1
                          have p339_1 := h339c.2.1
                          have p339_2 := h339c.2.2.1
                          have p339_3 := h339c.2.2.2
                          linarith only [hlam, p339_0]
                      · linarith only [h334, h338, hc34, hlam, hphi, u4elo1]
                    · linarith only [h258, h335, h337, h4, hc14, hlam, hphi, u4elo0]
                  · linarith only [h258, h3, h335, h336, h4, hc14, hlam, hphi, u4elo0]
                · linarith only [h335, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h334, h4, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
      · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
        · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
          · rcases m.htr 1 3 5 (by decide) (by decide) with h373 | h373
            · rcases m.htr 1 4 5 (by decide) (by decide) with h374 | h374
              · linarith only [h374, h4, hc04, hlam, hphi, u4elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h376 | h376
                · rcases m.htr 2 3 5 (by decide) (by decide) with h377 | h377
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                    · linarith only [h0, h372, h378, h4, hc34, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h380 | h380
                      · linarith only [h0, h372, h380, h4, hlam]
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
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p382_1, u4elo4]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p382_1, u4elo4]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p382_1, u4elo4]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h4, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h1, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h1, hc01, hc25, hlam, hphi, ht0b, ht5b, p382_1]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h1, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p382_1, u4elo4]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h374, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h2, hlam, p382_1]
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
                          linarith only [h2, hc02, hc35, hlam, hphi, ht0b, ht5b, p382_1]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h378, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h3, hlam, p382_1]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h373, hlam, p382_1]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h377, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h380, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p382_1, u4elo4]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h371, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p382_1, u4elo4]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h377, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p382_1, u4elo4]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p382_1, u4elo4]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hlam, p382_0]
                  · linarith only [h1, h373, h376, h377, h4, hc34, hlam, hphi, u4elo4]
                · linarith only [h0, h372, h376, h4, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h3, h372, h373, h4, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
            · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
              · linarith only [h0, h4, h412, hlam]
              · linarith only [h372, h411, h412, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h415 | h415
              · linarith only [h4, h415, hc04, hlam, hphi, u4elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h417 | h417
                · linarith only [h370, h372, h417, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h419 | h419
                  · linarith only [h370, h411, h419, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
                    · linarith only [h3, h370, h4, h411, h421, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h423 | h423
                      · linarith only [h3, h370, h4, h411, h423, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h370, h372, h423, hc23, hlam, hphi, ht34, u4elo4]
        · linarith only [h2, h370, h371, h4, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h427 | h427
        · rcases m.htr 1 3 4 (by decide) (by decide) with h428 | h428
          · rcases m.htr 1 3 5 (by decide) (by decide) with h429 | h429
            · rcases m.htr 1 4 5 (by decide) (by decide) with h430 | h430
              · linarith only [h0, h4, h430, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h432 | h432
                · rcases m.htr 2 3 5 (by decide) (by decide) with h433 | h433
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h434 | h434
                    · linarith only [h4, h434, hc04, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h436 | h436
                      · linarith only [h0, h4, h428, h436, hlam]
                      · rcases h5bigk with h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [hlam, p438_0]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h4, h427, h432, h434, hc34, hlam, hphi, p438_1, u4elo4]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h4, h432, h434, hc34, hlam, hphi, p438_1, u4elo4]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p438_1, u4elo4]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h4, hlam, p438_0]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h1, hlam, p438_0]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [hlam, p438_0]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h1, h432, h434, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p438_1]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h370, h427, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p438_1]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h430, hlam, p438_0]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h2, hlam, p438_1]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h427, hlam, p438_1]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [hlam, p438_0]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h2, hc02, hc35, hlam, hphi, ht0b, ht5b, p438_1]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h434, hlam, p438_0]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h3, hlam, p438_1]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h429, hlam, p438_1]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h433, hlam, p438_0]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [hlam, p438_0]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h436, hlam, p438_0]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p438_1, u4elo4]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p438_1, u4elo4]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [h433, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p438_1, u4elo4]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p438_1, u4elo4]
                        · have p438_0 := h438c.1
                          have p438_1 := h438c.2.1
                          have p438_2 := h438c.2.2.1
                          have p438_3 := h438c.2.2.2
                          linarith only [hlam, p438_0]
                  · linarith only [h3, h370, h4, h433, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h370, h427, h428, h432, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h3, h4, h428, h429, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h467 | h467
            · rcases m.htr 1 4 5 (by decide) (by decide) with h468 | h468
              · linarith only [h0, h4, h468, hlam]
              · linarith only [h370, h427, h428, h468, hlam]
            · linarith only [h370, h427, h467, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h472 | h472
          · rcases m.htr 1 3 5 (by decide) (by decide) with h473 | h473
            · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
              · linarith only [h4, h474, hc04, hlam, hphi, u4elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h476 | h476
                · rcases m.htr 2 3 5 (by decide) (by decide) with h477 | h477
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                    · linarith only [h2, h4, h427, h478, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h480 | h480
                      · linarith only [h0, h2, h4, h427, h472, h480, hc12, hlam, hphi, ht23, ht34, u4elo0]
                      · rcases h5bigk with h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p482_1, u4elo4]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h4, h427, hc12, hlam, hphi, ht23, ht34, p482_1, u4elo4]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p482_1, u4elo4]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h4, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h1, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h427, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p482_1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h474, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h2, hlam, p482_1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p482_1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h2, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p482_1, u4elo4]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h478, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h3, hlam, p482_1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h473, hlam, p482_1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h477, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h480, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p482_1, u4elo4]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h474, hc14, hlam, hphi, p482_1, u4elo4]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h427, hc12, hlam, hphi, ht23, ht34, p482_1, u4elo4]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p482_1, u4elo4]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                  · linarith only [h3, h370, h4, h477, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h370, h472, h476, hc12, hlam, hphi, ht23, ht34, u4elo1]
            · linarith only [h3, h4, h472, h473, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h511 | h511
            · rcases m.htr 1 4 5 (by decide) (by decide) with h512 | h512
              · linarith only [h0, h4, h512, hlam]
              · linarith only [h472, h511, h512, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h515 | h515
              · linarith only [h0, h4, h515, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h517 | h517
                · rcases m.htr 2 3 5 (by decide) (by decide) with h518 | h518
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h519 | h519
                    · linarith only [h4, h519, hc04, hlam, hphi, u4elo2]
                    · linarith only [h370, h472, h517, h519, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h370, h472, h517, h518, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h370, h517, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h524 | h524
    · rcases m.htr 1 2 3 (by decide) (by decide) with h525 | h525
      · rcases m.htr 1 2 5 (by decide) (by decide) with h526 | h526
        · rcases m.htr 1 3 4 (by decide) (by decide) with h527 | h527
          · rcases m.htr 1 3 5 (by decide) (by decide) with h528 | h528
            · linarith only [h1, h3, h528, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h530 | h530
              · linarith only [h527, h528, h530, hlam]
              · linarith only [h524, h530, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h533 | h533
            · linarith only [h3, h527, h533, hc03, hlam, hphi, ht34, u4elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h535 | h535
              · rcases m.htr 2 3 4 (by decide) (by decide) with h536 | h536
                · linarith only [h525, h527, h536, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h538 | h538
                  · linarith only [h3, h525, h527, h538, hc03, hlam, hphi, ht34, u4elo3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h540 | h540
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h541 | h541
                      · rcases h5bigk with h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [hlam, p542_0]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h3, h541, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p542_1, u4elo3]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h3, h541, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p542_1, u4elo3]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h3, hlam, p542_0]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h3, h541, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p542_1, u4elo3]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h1, hlam, p542_0]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [hlam, p542_0]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h1, hc01, hc25, hlam, hphi, ht0b, ht5b, p542_1]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h533, hlam, p542_0]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h1, h3, h541, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p542_1, u4elo3]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h2, hlam, p542_1]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h526, hlam, p542_1]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [hlam, p542_0]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h538, hlam, p542_1]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h526, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p542_1]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h541, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p542_1, u4elo3]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h526, h541, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p542_1, u4elo3]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h541, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p542_1, u4elo3]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [hlam, p542_0]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h541, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p542_1, u4elo3]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h524, hlam, p542_1]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h535, hlam, p542_1]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h540, hlam, p542_1]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [h541, hlam, p542_1]
                        · have p542_0 := h542c.1
                          have p542_1 := h542c.2.1
                          have p542_2 := h542c.2.2.1
                          have p542_3 := h542c.2.2.2
                          linarith only [hlam, p542_0]
                      · linarith only [h524, h536, h541, hc24, hlam, hphi, u4elo0]
                    · linarith only [h524, h536, h540, hc23, hlam, hphi, ht34, u4elo0]
              · linarith only [h524, h535, hc14, hlam, hphi, u4elo0]
        · linarith only [h2, h524, h525, h526, hc23, hlam, hphi, ht34, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h572 | h572
        · rcases m.htr 1 3 4 (by decide) (by decide) with h573 | h573
          · rcases m.htr 1 3 5 (by decide) (by decide) with h574 | h574
            · linarith only [h1, h3, h574, hlam]
            · linarith only [h525, h572, h574, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h577 | h577
            · linarith only [h3, h573, h577, hc03, hlam, hphi, ht34, u4elo3]
            · linarith only [h525, h572, h577, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h580 | h580
          · rcases m.htr 1 3 5 (by decide) (by decide) with h581 | h581
            · linarith only [h1, h3, h581, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h583 | h583
              · linarith only [h580, h581, h583, hlam]
              · linarith only [h524, h583, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h586 | h586
            · linarith only [h3, h580, h586, hc03, hlam, hphi, ht34, u4elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h588 | h588
              · rcases m.htr 2 3 4 (by decide) (by decide) with h589 | h589
                · rcases m.htr 2 3 5 (by decide) (by decide) with h590 | h590
                  · linarith only [h2, h3, h590, hlam]
                  · linarith only [h580, h589, h590, hc13, hc35, hlam, hphi]
                · linarith only [h525, h589, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h524, h588, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
      · rcases m.htr 1 2 5 (by decide) (by decide) with h596 | h596
        · rcases m.htr 1 3 4 (by decide) (by decide) with h597 | h597
          · rcases m.htr 1 3 5 (by decide) (by decide) with h598 | h598
            · linarith only [h1, h3, h598, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h600 | h600
              · linarith only [h524, h600, hc04, hlam, hphi, u4elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h602 | h602
                · rcases m.htr 2 3 5 (by decide) (by decide) with h603 | h603
                  · linarith only [h1, h3, h595, h598, h603, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h605 | h605
                    · linarith only [h0, h524, h597, h605, hc34, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                      · linarith only [h0, h597, h605, h607, hc24, hlam, hphi, u4elo0]
                      · linarith only [h595, h598, h602, h607, hc34, hlam, hphi, u4elo4]
                · linarith only [h597, h598, h602, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
            · linarith only [h0, h3, h524, h597, h611, hc03, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h613 | h613
              · linarith only [h0, h524, h613, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h615 | h615
                · linarith only [h0, h524, h595, h597, h615, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h617 | h617
                  · linarith only [h0, h3, h524, h595, h597, h617, hc03, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h619 | h619
                    · linarith only [h524, h619, hc04, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h621 | h621
                      · linarith only [h0, h524, h595, h597, h621, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h595, h597, h621, hc23, hlam, hphi, ht34, u4elo4]
        · linarith only [h2, h524, h595, h596, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
        · rcases m.htr 1 3 4 (by decide) (by decide) with h626 | h626
          · rcases m.htr 1 3 5 (by decide) (by decide) with h627 | h627
            · linarith only [h1, h3, h627, hlam]
            · linarith only [h595, h625, h627, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h630 | h630
            · linarith only [h0, h3, h524, h626, h630, hc03, hlam, hphi, ht34, u4elo4]
            · linarith only [h595, h625, h630, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h633 | h633
          · rcases m.htr 1 3 5 (by decide) (by decide) with h634 | h634
            · linarith only [h1, h3, h634, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h636 | h636
              · linarith only [h0, h524, h636, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h638 | h638
                · rcases m.htr 2 3 5 (by decide) (by decide) with h639 | h639
                  · linarith only [h2, h3, h639, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h641 | h641
                    · linarith only [h524, h641, hc04, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h643 | h643
                      · linarith only [h0, h2, h524, h595, h633, h639, h643, hc12, hlam, hphi, ht23, ht34, u4elo0]
                      · linarith only [h595, h639, h643, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h595, h633, h638, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h647 | h647
            · linarith only [h0, h3, h524, h633, h647, hc03, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h649 | h649
              · linarith only [h0, h524, h649, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h651 | h651
                · rcases m.htr 2 3 5 (by decide) (by decide) with h652 | h652
                  · linarith only [h2, h3, h652, hlam]
                  · linarith only [h595, h633, h651, h652, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h595, h651, hc12, hlam, hphi, ht23, ht34, u4elo3]

end R2N4
