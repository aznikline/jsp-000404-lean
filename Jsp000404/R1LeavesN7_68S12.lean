import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h10, h12, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases h0bigk with h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h5, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h0, hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h5, h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14_1, u2elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14_1, u2elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h1, hlam, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h3, hlam, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14_1, u2elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h4, hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h5, hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14_1, u2elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h2, hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p14_1, u5elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h6, hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h7, hlam, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hlam, p14_0]
                      · linarith only [h0, h10, h11, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
                      · linarith only [h10, h3, h41, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                        · rcases h0bigk with h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, h41, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h41, h43, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h41, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h1, h41, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p44_1, u2elo0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h41, h43, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p44_1, u2elo0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h2, h41, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p44_1, u2elo0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h1, hlam, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h3, hlam, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h2, h41, h7, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h2, h3, h41, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p44_1, u2elo0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h4, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h5, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h2, h3, h41, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p44_1, u2elo0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h2, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p44_1, u5elo0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h6, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h7, hlam, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                        · linarith only [h10, h3, h43, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                    · linarith only [h3, h6, h71, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
                      · linarith only [h73, h8, h9, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                        · rcases h0bigk with h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [hlam, p76_0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h3, h5, h75, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h5, h75, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h5, h75, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h0, hlam, p76_0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [hlam, p76_0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h5, h75, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p76_1, u2elo0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h5, h75, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p76_1, u2elo0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h6, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p76_1, u2elo0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h1, hlam, p76_1]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h3, hlam, p76_1]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [hlam, p76_0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h5, h75, h8, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h3, h6, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p76_1, u2elo0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h4, hlam, p76_0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h5, hlam, p76_0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [hlam, p76_0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h3, h5, h6, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p76_1, u2elo0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h2, hlam, p76_0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p76_1, u5elo0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h6, hlam, p76_0]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [h7, hlam, p76_1]
                          · have p76_0 := h76c.1
                            have p76_1 := h76c.2.1
                            have p76_2 := h76c.2.2.1
                            have p76_3 := h76c.2.2.2
                            linarith only [hlam, p76_0]
                        · linarith only [h3, h5, h7, h71, h75, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
                · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                        · linarith only [h0, h104, h106, h108, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h0, h104, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            rcases p110_3 (m.d 0 1) (by simp) with h114 | h114
                            · rcases p110_3 (m.d 0 2) (by simp) with h115 | h115
                              · linarith only [h0, h115, hlam]
                              · linarith only [h115, h4, hlam]
                            · linarith only [h114, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            rcases p110_3 (m.d 0 1) (by simp) with h119 | h119
                            · rcases p110_3 (m.d 0 2) (by simp) with h120 | h120
                              · linarith only [h0, h120, hlam]
                              · linarith only [h0, h104, h107, h108, h120, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p110_1]
                            · linarith only [h119, h2, hlam]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h0, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h1, h104, h107, h108, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p110_1, u2elo0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h106, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p110_1, u2elo0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h1, hlam, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h3, hlam, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h106, h3, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p110_1, u2elo0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h2, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h7, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h4, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h5, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
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
                            linarith only [h0, h104, h107, h108, h7, hc34, hlam, hphi, ht45, p110_1, u5elo4]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h6, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h7, hc04, hlam, hphi, ht45, p110_1, u5elo4]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                      · linarith only [h1, h105, h106, h107, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · linarith only [h106, h5, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                    · linarith only [h104, h105, h146, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · linarith only [h146, h5, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h104, h3, hc12, hlam, hphi, u2elo0]
            · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h151 | h151
            · rcases m.htr 0 4 5 (by decide) (by decide) with h152 | h152
              · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
                · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                    · linarith only [h1, h153, h154, h155, h5, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h157 | h157
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                        · rcases h0bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, h153, h157, h158, hc01, hc45, hlam, hphi, ht0b, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h1, h153, h157, h158, hc01, hc45, hlam, hphi, ht0b, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h1, h153, h157, h158, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            rcases p159_3 (m.d 0 1) (by simp) with h164 | h164
                            · rcases p159_3 (m.d 0 2) (by simp) with h165 | h165
                              · linarith only [h0, h165, hlam]
                              · linarith only [h0, h153, h157, h158, h165, hc01, hc45, hlam, hphi, ht0b, ht5b, p159_1]
                            · linarith only [h164, h2, hlam]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h1, h153, h157, h158, hc02, hc45, hlam, hphi, ht0b, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h1, h153, h157, h158, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p159_1, u2elo0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p159_1, u2elo0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h1, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h3, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h5, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h2, h5, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h4, hc01, hlam, hphi, ht12, p159_1, u2elo0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h4, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p159_1, u2elo0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h154, h158, h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p159_1, u2elo0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h2, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p159_1, u5elo0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h151, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h152, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                        · linarith only [h157, h158, h3, h5, hc35, hlam, hphi, u5elo4]
                      · linarith only [h151, h157, h5, hc23, hc34, hlam, hphi]
                  · linarith only [h151, h153, h154, h5, hc23, hc34, hlam, hphi]
                · linarith only [h153, h3, hc12, hlam, hphi, u2elo0]
              · linarith only [h151, h152, h5, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
              · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                · rcases m.htr 1 3 5 (by decide) (by decide) with h196 | h196
                  · linarith only [h1, h151, h196, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                    · linarith only [h151, h198, h3, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h200 | h200
                      · linarith only [h1, h151, h195, h200, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h202 | h202
                        · rcases h0bigk with h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [hlam, p203_0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h0, h195, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p203_1]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            rcases p203_3 (m.d 0 1) (by simp) with h206 | h206
                            · rcases p203_3 (m.d 0 2) (by simp) with h207 | h207
                              · linarith only [h0, h207, hlam]
                              · linarith only [h207, h3, hlam]
                            · linarith only [h1, h206, hlam]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h194, hc01, hc45, hlam, hphi, ht0b, ht5b, p203_1]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            rcases p203_3 (m.d 0 1) (by simp) with h212 | h212
                            · rcases p203_3 (m.d 0 2) (by simp) with h213 | h213
                              · linarith only [h0, h213, hlam]
                              · linarith only [h0, h195, h213, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p203_1]
                            · linarith only [h2, h212, hlam]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h0, hlam, p203_0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [hlam, p203_0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p203_1, u2elo0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h194, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p203_1, u2elo0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p203_1, u2elo0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h1, hlam, p203_1]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h3, hlam, p203_1]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [hlam, p203_0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h5, hlam, p203_1]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h151, hlam, p203_1]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h0, h195, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p203_1]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h4, hlam, p203_0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h1, h195, h5, hc23, hc34, hlam, hphi, p203_1]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [hlam, p203_0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h1, h151, h195, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p203_1, u2elo0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h2, hlam, p203_0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p203_1, u5elo0]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h1, h151, h195, hc23, hlam, hphi, ht34, ht45, p203_1, u5elo3]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [h194, hlam, p203_1]
                          · have p203_0 := h203c.1
                            have p203_1 := h203c.2.1
                            have p203_2 := h203c.2.2.1
                            have p203_3 := h203c.2.2.2
                            linarith only [hlam, p203_0]
                        · linarith only [h1, h195, h202, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h195, h3, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
                · rcases m.htr 1 3 5 (by decide) (by decide) with h240 | h240
                  · linarith only [h1, h151, h194, h240, h5, hc05, hlam, hphi, u5elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
                    · linarith only [h0, h239, h242, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h244 | h244
                      · linarith only [h1, h151, h239, h244, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h246 | h246
                        · rcases h0bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h0, h239, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            rcases p247_3 (m.d 0 1) (by simp) with h250 | h250
                            · rcases p247_3 (m.d 0 2) (by simp) with h251 | h251
                              · linarith only [h0, h251, hlam]
                              · linarith only [h251, h3, hlam]
                            · linarith only [h1, h250, hlam]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            rcases p247_3 (m.d 0 1) (by simp) with h255 | h255
                            · rcases p247_3 (m.d 0 2) (by simp) with h256 | h256
                              · linarith only [h0, h256, hlam]
                              · linarith only [h256, h4, hlam]
                            · linarith only [h255, hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            rcases p247_3 (m.d 0 1) (by simp) with h260 | h260
                            · rcases p247_3 (m.d 0 2) (by simp) with h261 | h261
                              · linarith only [h0, h261, hlam]
                              · linarith only [h0, h239, h261, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1]
                            · linarith only [h2, h260, hlam]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h0, hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p247_1, u2elo0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p247_1, u2elo0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p247_1, u2elo0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h1, hlam, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h3, hlam, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h5, hlam, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h151, hlam, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h194, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p247_1, u5elo0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h4, hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h194, hc03, hlam, hphi, ht34, ht45, p247_1, u5elo0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h194, hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h2, hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h194, h246, hc02, hlam, hphi, ht23, ht34, ht45, p247_1, u5elo3]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h194, h246, hc03, hlam, hphi, ht34, ht45, p247_1, u5elo3]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h194, h246, hc04, hlam, hphi, ht45, p247_1, u5elo3]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hlam, p247_0]
                        · linarith only [h1, h239, h246, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h239, h3, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h287 | h287
          · linarith only [h287, h3, h4, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
            · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
              · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
                · rcases m.htr 1 3 5 (by decide) (by decide) with h292 | h292
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h293 | h293
                    · linarith only [h0, h287, h291, h293, h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h295 | h295
                      · linarith only [h0, h291, h295, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · linarith only [h1, h292, h295, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h289, h292, h3, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h291, h3, h4, hc12, hlam, hphi, u2elo3]
              · linarith only [h290, h3, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h301 | h301
              · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
                · rcases m.htr 1 3 5 (by decide) (by decide) with h303 | h303
                  · linarith only [h1, h289, h303, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h305 | h305
                    · linarith only [h1, h289, h302, h305, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                      · linarith only [h0, h289, h302, h307, h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h309 | h309
                        · rcases h0bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 1) (by simp) with h313 | h313
                            · rcases p310_3 (m.d 0 2) (by simp) with h314 | h314
                              · linarith only [h0, h314, hlam]
                              · linarith only [h3, h314, hlam]
                            · linarith only [h1, h313, hlam]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h0, h302, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 1) (by simp) with h319 | h319
                            · rcases p310_3 (m.d 0 2) (by simp) with h320 | h320
                              · linarith only [h0, h320, hlam]
                              · linarith only [h0, h302, h320, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1]
                            · linarith only [h2, h319, hlam]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h0, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h1, h302, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p310_1, u2elo0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h4, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p310_1, u2elo3]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h1, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h3, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h287, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h289, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h0, h302, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h4, hc02, hlam, hphi, p310_1, u2elo3]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h1, h302, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p310_1, u2elo3]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h1, h289, h302, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p310_1, u2elo3]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h2, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h0, h302, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h1, h289, h302, hc23, hc35, hlam, hphi, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h301, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                        · linarith only [h301, h305, h309, h4, hlam]
                · linarith only [h3, h302, hc12, hlam, hphi, u2elo0]
              · linarith only [h3, h301, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h347 | h347
        · rcases m.htr 0 3 4 (by decide) (by decide) with h348 | h348
          · rcases m.htr 0 3 5 (by decide) (by decide) with h349 | h349
            · rcases m.htr 0 4 5 (by decide) (by decide) with h350 | h350
              · rcases m.htr 1 2 3 (by decide) (by decide) with h351 | h351
                · linarith only [h0, h3, h347, h351, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h354 | h354
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h355 | h355
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
                        · linarith only [h3, h347, h354, h356, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · linarith only [h3, h347, h350, h356, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h1, h3, h347, h353, h355, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h3, h348, h354, hlam]
                  · linarith only [h3, h347, h349, h350, h351, h353, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
                · linarith only [h3, h362, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h364 | h364
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h365 | h365
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h366 | h366
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
                        · linarith only [h3, h347, h365, h367, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
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
                            linarith only [h347, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h3, h347, h365, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            rcases p369_3 (m.d 0 1) (by simp) with h373 | h373
                            · rcases p369_3 (m.d 0 2) (by simp) with h374 | h374
                              · linarith only [h0, h374, hlam]
                              · linarith only [h347, h374, hlam]
                            · linarith only [h373, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            rcases p369_3 (m.d 0 1) (by simp) with h378 | h378
                            · rcases p369_3 (m.d 0 2) (by simp) with h379 | h379
                              · linarith only [h0, h379, hlam]
                              · linarith only [h347, h365, h379, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p369_1]
                            · linarith only [h2, h378, hlam]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h0, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h3, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h3, h347, h365, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p369_1, u2elo2]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h3, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p369_1, u2elo2]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h1, hlam, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h0, h3, hc12, hlam, hphi, p369_1, u2elo2]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h3, h347, h365, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p369_1, u2elo2]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h3, h347, h350, h365, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p369_1, u2elo2]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h350, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h347, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h348, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h350, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h2, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h347, h349, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p369_1]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h349, hlam, p369_0]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [h350, hc04, hlam, hphi, ht45, p369_1, u5elo4]
                          · have p369_0 := h369c.1
                            have p369_1 := h369c.2.1
                            have p369_2 := h369c.2.2.1
                            have p369_3 := h369c.2.2.2
                            linarith only [hlam, p369_0]
                      · linarith only [h1, h3, h364, h366, hlam]
                    · linarith only [h3, h347, h348, h365, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h3, h349, h362, h364, hc12, hlam, hphi, u2elo2]
            · linarith only [h3, h347, h349, hc24, hlam, hphi, ht45, u5elo3]
          · linarith only [h3, h347, h348, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h408 | h408
          · rcases m.htr 0 3 5 (by decide) (by decide) with h409 | h409
            · rcases m.htr 0 4 5 (by decide) (by decide) with h410 | h410
              · rcases m.htr 1 2 3 (by decide) (by decide) with h411 | h411
                · linarith only [h0, h3, h411, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h413 | h413
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h414 | h414
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h415 | h415
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
                        · rcases h0bigk with h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [hlam, p417_0]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            rcases p417_3 (m.d 0 1) (by simp) with h419 | h419
                            · rcases p417_3 (m.d 0 2) (by simp) with h420 | h420
                              · linarith only [h0, h420, hlam]
                              · rcases p417_3 (m.d 0 3) (by simp) with h422 | h422
                                · linarith only [h1, h422, hlam]
                                · linarith only [h3, h422, hlam]
                            · linarith only [h0, h419, hlam]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h408, h416, hc01, hc45, hlam, hphi, ht0b, ht5b, p417_1]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h408, h416, hc01, hc45, hlam, hphi, ht0b, ht5b, p417_1]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            rcases p417_3 (m.d 0 1) (by simp) with h428 | h428
                            · rcases p417_3 (m.d 0 2) (by simp) with h429 | h429
                              · linarith only [h0, h429, hlam]
                              · rcases p417_3 (m.d 0 3) (by simp) with h431 | h431
                                · linarith only [h1, h431, hlam]
                                · linarith only [h409, h431, hlam]
                            · linarith only [h2, h428, hlam]
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
                            linarith only [h3, hlam, p417_0]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h347, hlam, p417_1]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p417_1, u2elo0]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h1, hlam, p417_1]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h0, h3, hc12, hlam, hphi, p417_1, u2elo2]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [hlam, p417_0]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h3, h408, h416, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p417_1, u2elo2]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h2, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p417_1, u2elo2]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p417_1]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h0, h347, h414, hc12, hlam, hphi, p417_1, u2elo2]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h408, hlam, p417_0]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [hlam, p417_0]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h2, h347, h413, h414, h416, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p417_1, u2elo2]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h2, hlam, p417_0]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p417_1, u5elo0]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h409, hlam, p417_0]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [h410, hlam, p417_1]
                          · have p417_0 := h417c.1
                            have p417_1 := h417c.2.1
                            have p417_2 := h417c.2.2.1
                            have p417_3 := h417c.2.2.2
                            linarith only [hlam, p417_0]
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
                            rcases p455_3 (m.d 0 1) (by simp) with h457 | h457
                            · rcases p455_3 (m.d 0 2) (by simp) with h458 | h458
                              · linarith only [h0, h458, hlam]
                              · rcases p455_3 (m.d 0 3) (by simp) with h460 | h460
                                · linarith only [h1, h460, hlam]
                                · linarith only [h3, h460, hlam]
                            · linarith only [h0, h457, hlam]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h1, h413, h416, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p455_1]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h410, h416, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p455_1]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h410, h416, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p455_1]
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
                            linarith only [h347, hlam, p455_1]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h410, h416, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p455_1]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h1, hlam, p455_1]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h0, h3, hc12, hlam, hphi, p455_1, u2elo2]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [hlam, p455_0]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h3, h410, h416, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p455_1, u2elo2]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h3, h410, h416, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p455_1, u2elo2]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h347, hc01, hlam, hphi, ht12, p455_1, u2elo3]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h0, h347, hc12, hlam, hphi, p455_1, u2elo3]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h408, hlam, p455_0]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [hlam, p455_0]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h3, h408, h410, h416, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p455_1, u2elo2]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h2, hlam, p455_0]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p455_1, u5elo0]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h409, hlam, p455_0]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [h410, hlam, p455_1]
                          · have p455_0 := h455c.1
                            have p455_1 := h455c.2.1
                            have p455_2 := h455c.2.2.1
                            have p455_3 := h455c.2.2.2
                            linarith only [hlam, p455_0]
                      · linarith only [h3, h408, h410, h413, h415, hc45, hlam, hphi, u5elo1]
                    · linarith only [h3, h408, h414, hlam]
                  · linarith only [h3, h409, h411, h413, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
                · linarith only [h0, h3, h347, h409, h490, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h492 | h492
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h493 | h493
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h494 | h494
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h495 | h495
                        · linarith only [h408, h410, h495, hlam]
                        · rcases h0bigk with h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            rcases p497_3 (m.d 0 1) (by simp) with h499 | h499
                            · rcases p497_3 (m.d 0 2) (by simp) with h500 | h500
                              · linarith only [h0, h500, hlam]
                              · rcases p497_3 (m.d 0 3) (by simp) with h502 | h502
                                · linarith only [h1, h502, hlam]
                                · linarith only [h3, h502, hlam]
                            · linarith only [h0, h499, hlam]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h1, h492, h495, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p497_1]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            rcases p497_3 (m.d 0 1) (by simp) with h507 | h507
                            · rcases p497_3 (m.d 0 2) (by simp) with h508 | h508
                              · linarith only [h0, h508, hlam]
                              · rcases p497_3 (m.d 0 3) (by simp) with h510 | h510
                                · linarith only [h1, h510, hlam]
                                · linarith only [h408, h510, hlam]
                            · linarith only [h507, hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            rcases p497_3 (m.d 0 1) (by simp) with h514 | h514
                            · rcases p497_3 (m.d 0 2) (by simp) with h515 | h515
                              · linarith only [h0, h515, hlam]
                              · rcases p497_3 (m.d 0 3) (by simp) with h517 | h517
                                · linarith only [h1, h517, hlam]
                                · linarith only [h409, h517, hlam]
                            · linarith only [h2, h514, hlam]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h0, hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h3, hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h347, hlam, p497_1]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h347, h410, hlam, p497_1]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h1, hlam, p497_1]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h3, hc02, hlam, hphi, p497_1, u2elo2]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h0, h3, h347, hc12, hlam, hphi, p497_1, u2elo2]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h0, h3, h347, h410, hc12, hlam, hphi, p497_1, u2elo2]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h410, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p497_1, u5elo0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h0, h410, hc12, hlam, hphi, ht23, ht34, ht45, p497_1, u5elo0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h408, hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h410, hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h2, hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h0, h410, hc12, hlam, hphi, ht23, ht34, ht45, p497_1, u5elo4]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h409, hlam, p497_0]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [h410, hc04, hlam, hphi, ht45, p497_1, u5elo4]
                          · have p497_0 := h497c.1
                            have p497_1 := h497c.2.1
                            have p497_2 := h497c.2.2.1
                            have p497_3 := h497c.2.2.2
                            linarith only [hlam, p497_0]
                      · linarith only [h1, h3, h492, h494, hlam]
                    · linarith only [h3, h408, h493, hlam]
                  · linarith only [h3, h409, h490, h492, hc12, hlam, hphi, u2elo2]
            · linarith only [h408, h409, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h545 | h545
            · rcases m.htr 0 4 5 (by decide) (by decide) with h546 | h546
              · rcases m.htr 1 2 3 (by decide) (by decide) with h547 | h547
                · linarith only [h0, h3, h547, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h549 | h549
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
                    · linarith only [h1, h408, h547, h550, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h552 | h552
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h553 | h553
                        · rcases h0bigk with h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [hlam, p554_0]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            rcases p554_3 (m.d 0 1) (by simp) with h556 | h556
                            · rcases p554_3 (m.d 0 2) (by simp) with h557 | h557
                              · linarith only [h0, h557, hlam]
                              · rcases p554_3 (m.d 0 3) (by simp) with h559 | h559
                                · linarith only [h1, h559, hlam]
                                · linarith only [h3, h559, hlam]
                            · linarith only [h0, h556, hlam]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h1, h549, h553, hc01, hc45, hlam, hphi, ht0b, ht5b, p554_1]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h1, h408, h549, h553, hc01, hc45, hlam, hphi, ht0b, ht5b, p554_1]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            rcases p554_3 (m.d 0 1) (by simp) with h565 | h565
                            · rcases p554_3 (m.d 0 2) (by simp) with h566 | h566
                              · linarith only [h0, h566, hlam]
                              · rcases p554_3 (m.d 0 3) (by simp) with h568 | h568
                                · linarith only [h1, h568, hlam]
                                · linarith only [h545, h568, hlam]
                            · linarith only [h2, h565, hlam]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h0, hlam, p554_0]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [hlam, p554_0]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h3, hlam, p554_0]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h347, hlam, p554_1]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p554_1, u2elo0]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h1, hlam, p554_1]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h0, h3, h550, hc12, hc34, hlam, hphi, ht23, p554_1]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [hlam, p554_0]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h408, hlam, p554_1]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h2, h3, h550, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p554_1]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h347, hc01, hlam, hphi, ht12, p554_1, u2elo3]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h0, h347, hc12, hlam, hphi, p554_1, u2elo3]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h347, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p554_1, u2elo3]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [hlam, p554_0]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h2, h347, h549, h553, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p554_1, u2elo3]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h2, hlam, p554_0]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p554_1, u5elo0]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h545, hlam, p554_0]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [h546, hlam, p554_1]
                          · have p554_0 := h554c.1
                            have p554_1 := h554c.2.1
                            have p554_2 := h554c.2.2.1
                            have p554_3 := h554c.2.2.2
                            linarith only [hlam, p554_0]
                        · linarith only [h550, h553, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h1, h3, h549, h552, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h408, h545, h549, hc13, hc34, hlam, hphi]
              · linarith only [h408, h545, h546, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h596 | h596
              · rcases m.htr 1 2 3 (by decide) (by decide) with h597 | h597
                · linarith only [h0, h3, h597, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h599 | h599
                  · linarith only [h1, h545, h599, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h601 | h601
                    · linarith only [h0, h3, h408, h601, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h603 | h603
                      · linarith only [h0, h3, h545, h601, h603, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h3, h603, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                · linarith only [h0, h3, h606, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h608 | h608
                  · linarith only [h1, h408, h596, h608, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h610 | h610
                    · linarith only [h0, h3, h408, h610, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h612 | h612
                      · linarith only [h1, h545, h610, h612, hc13, hc34, hlam, hphi]
                      · linarith only [h0, h3, h612, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h616 | h616
    · rcases m.htr 0 2 3 (by decide) (by decide) with h617 | h617
      · linarith only [h0, h1, h617, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h619 | h619
        · rcases m.htr 0 3 4 (by decide) (by decide) with h620 | h620
          · rcases m.htr 0 3 5 (by decide) (by decide) with h621 | h621
            · rcases m.htr 0 4 5 (by decide) (by decide) with h622 | h622
              · rcases m.htr 1 2 3 (by decide) (by decide) with h623 | h623
                · linarith only [h0, h1, h617, h623, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h623, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h626 | h626
                · linarith only [h0, h1, h617, h626, hlam]
                · linarith only [h0, h1, h626, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h621, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h0, h1, h619, h620, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h631 | h631
          · rcases m.htr 0 3 5 (by decide) (by decide) with h632 | h632
            · rcases m.htr 0 4 5 (by decide) (by decide) with h633 | h633
              · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
                · linarith only [h0, h1, h617, h634, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h634, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
                · linarith only [h0, h1, h617, h637, hlam]
                · linarith only [h0, h1, h637, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h632, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h641 | h641
            · rcases m.htr 0 4 5 (by decide) (by decide) with h642 | h642
              · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
                · linarith only [h0, h1, h631, h643, hc23, hc34, hlam, hphi]
                · linarith only [h0, h1, h643, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h1, h631, h642, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h0, h1, h641, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · linarith only [h0, h616, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

end R2N4
