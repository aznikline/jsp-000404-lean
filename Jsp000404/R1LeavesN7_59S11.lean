import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3548000 in
set_option maxHeartbeats 3548000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h1, h10, h13, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
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
                              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h11, h13, h2, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h11, h13, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hc01, hlam, hphi, ht0b, ht5b, p15_1, u5ehi0]
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
                              linarith only [h11, h13, h2, h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h0, h11, h13, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p15_1, u5ehi1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h1, hlam, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h4, hlam, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h11, h13, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p15_1, u3elo0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p15_1, u3elo0, u5ehi1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h2, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h5, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h7, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h3, hc04, hlam, hphi, ht0b, ht5b, p15_1, u5ehi1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h3, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h6, hlam, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h8, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h9, hlam, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                        · linarith only [h12, h7, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                          · linarith only [h10, h11, h43, hlam]
                          · rcases h0bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h4, h42, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h4, h42, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h10, h11, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [hc01, hlam, hphi, ht0b, ht5b, p45_1, u5ehi0]
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
                              linarith only [h8, hc02, hlam, hphi, ht0b, ht5b, p45_1, u5ehi3]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h0, h10, h11, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p45_1, u5ehi1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h1, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h4, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p45_1, u3elo0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo0, u5ehi1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h2, hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h5, hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h7, hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h3, hc04, hlam, hphi, ht0b, ht5b, p45_1, u5ehi1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h3, hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h6, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h8, hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h9, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [hlam, p45_0]
                        · linarith only [h42, h7, hc23, hlam, hphi, u3elo0]
                    · linarith only [h10, h7, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
                      · linarith only [h2, h74, h9, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                          · linarith only [h6, h76, h77, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                          · rcases h0bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p79_1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h4, h76, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              rcases p79_3 (m.d 0 1) (by simp) with h83 | h83
                              · rcases p79_3 (m.d 0 2) (by simp) with h84 | h84
                                · linarith only [h0, h84, hlam]
                                · linarith only [h5, h84, hlam]
                              · linarith only [h2, h83, hlam]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p79_1, u5ehi1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h0, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h8, hc02, hlam, hphi, ht0b, ht5b, p79_1, u5ehi3]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              rcases p79_3 (m.d 0 1) (by simp) with h92 | h92
                              · rcases p79_3 (m.d 0 2) (by simp) with h93 | h93
                                · rcases p79_3 (m.d 0 3) (by simp) with h94 | h94
                                  · linarith only [h4, h94, hlam]
                                  · linarith only [h7, h94, hlam]
                                · linarith only [h5, h93, hlam]
                              · linarith only [h2, h92, hlam]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p79_1, u5ehi1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h1, hlam, p79_1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h4, hlam, p79_1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h2, h73, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p79_1, u3elo0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p79_1, u3elo0, u5ehi1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h2, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h5, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h7, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h9, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h3, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h6, hlam, p79_1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h8, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h2, h73, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p79_1, u3elo0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [hlam, p79_0]
                        · linarith only [h73, h76, hc23, hlam, hphi, u3elo1]
                    · linarith only [h7, h73, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h117 | h117
                  · linarith only [h117, h7, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                      · linarith only [h1, h117, h119, h120, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                          · linarith only [h117, h123, h7, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · rcases h0bigk with h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              rcases p125_3 (m.d 0 1) (by simp) with h129 | h129
                              · rcases p125_3 (m.d 0 2) (by simp) with h130 | h130
                                · linarith only [h0, h130, hlam]
                                · linarith only [h130, h5, hlam]
                              · linarith only [h129, h2, hlam]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h1, h119, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h0, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h1, h119, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              rcases p125_3 (m.d 0 1) (by simp) with h138 | h138
                              · rcases p125_3 (m.d 0 2) (by simp) with h139 | h139
                                · rcases p125_3 (m.d 0 3) (by simp) with h140 | h140
                                  · linarith only [h140, h4, hlam]
                                  · linarith only [h140, h7, hlam]
                                · linarith only [h139, h5, hlam]
                              · linarith only [h138, h2, hlam]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h0, h1, h119, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h1, hlam, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h4, hlam, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h119, h2, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p125_1, u3elo4]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h8, hlam, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h2, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h5, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h7, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h117, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h3, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h6, hlam, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h1, h119, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h119, h2, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p125_1, u3elo4]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [hlam, p125_0]
                        · linarith only [h1, h119, h122, hc23, hlam, hphi, u3elo0]
                    · linarith only [h119, h7, h8, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
                · linarith only [h163, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h166 | h166
                    · linarith only [h166, h7, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h168 | h168
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                        · linarith only [h168, h169, h2, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h171 | h171
                          · rcases h0bigk with h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p172_1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              rcases p172_3 (m.d 0 1) (by simp) with h175 | h175
                              · rcases p172_3 (m.d 0 2) (by simp) with h176 | h176
                                · linarith only [h0, h176, hlam]
                                · linarith only [h176, h4, hlam]
                              · linarith only [h1, h175, hlam]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h168, h2, hc01, hlam, hphi, ht0b, ht5b, p172_1, u5ehi4]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hc01, hlam, hphi, ht0b, ht5b, p172_1, u5ehi0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h0, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              rcases p172_3 (m.d 0 1) (by simp) with h184 | h184
                              · rcases p172_3 (m.d 0 2) (by simp) with h185 | h185
                                · rcases p172_3 (m.d 0 3) (by simp) with h186 | h186
                                  · linarith only [h186, h4, hlam]
                                  · rcases p172_3 (m.d 0 4) (by simp) with h188 | h188
                                    · linarith only [h188, h5, hlam]
                                    · linarith only [h188, h7, hlam]
                                · linarith only [h185, h4, hlam]
                              · linarith only [h1, h184, hlam]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h168, h2, hc02, hlam, hphi, ht0b, ht5b, p172_1, u5ehi4]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h0, h168, h3, hc01, hlam, hphi, ht0b, ht5b, p172_1, u5ehi4]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h1, hlam, p172_1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h4, hlam, p172_1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h7, hlam, p172_1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h163, hlam, p172_1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h2, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h5, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h1, h7, hc13, hlam, hphi, p172_1, u3elo3]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h168, h3, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p172_1, u3elo3, u5ehi4]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h3, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h6, hlam, p172_1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h1, h163, h171, hc13, hlam, hphi, p172_1, u3elo3]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h165, hlam, p172_1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hlam, p172_0]
                          · linarith only [h165, h168, h171, h2, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · linarith only [h165, h166, h168, h7, hc13, hlam, hphi, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h212 | h212
                    · linarith only [h1, h212, h7, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h214 | h214
                      · linarith only [h165, h2, h214, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h216 | h216
                        · linarith only [h216, h4, h7, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h218 | h218
                          · linarith only [h165, h218, h7, hc03, hlam, hphi, u3elo3]
                          · rcases h0bigk with h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [hlam, p220_0]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p220_1]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              rcases p220_3 (m.d 0 1) (by simp) with h223 | h223
                              · rcases p220_3 (m.d 0 2) (by simp) with h224 | h224
                                · linarith only [h0, h224, hlam]
                                · linarith only [h224, h4, hlam]
                              · linarith only [h1, h223, hlam]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              rcases p220_3 (m.d 0 1) (by simp) with h228 | h228
                              · rcases p220_3 (m.d 0 2) (by simp) with h229 | h229
                                · linarith only [h0, h229, hlam]
                                · linarith only [h229, h5, hlam]
                              · linarith only [h2, h228, hlam]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [hc01, hlam, hphi, ht0b, ht5b, p220_1, u5ehi0]
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
                              rcases p220_3 (m.d 0 1) (by simp) with h236 | h236
                              · rcases p220_3 (m.d 0 2) (by simp) with h237 | h237
                                · rcases p220_3 (m.d 0 3) (by simp) with h238 | h238
                                  · linarith only [h238, h4, hlam]
                                  · rcases p220_3 (m.d 0 4) (by simp) with h240 | h240
                                    · linarith only [h240, h5, hlam]
                                    · linarith only [h240, h7, hlam]
                                · linarith only [h237, h4, hlam]
                              · linarith only [h1, h236, hlam]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              rcases p220_3 (m.d 0 1) (by simp) with h245 | h245
                              · rcases p220_3 (m.d 0 2) (by simp) with h246 | h246
                                · rcases p220_3 (m.d 0 3) (by simp) with h247 | h247
                                  · linarith only [h247, h4, hlam]
                                  · rcases p220_3 (m.d 0 4) (by simp) with h249 | h249
                                    · linarith only [h249, h5, hlam]
                                    · rcases p220_3 (m.d 0 5) (by simp) with h251 | h251
                                      · linarith only [h251, h6, hlam]
                                      · linarith only [h165, h251, hlam]
                                · linarith only [h246, h5, hlam]
                              · linarith only [h2, h245, hlam]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h3, hc02, hlam, hphi, ht0b, ht5b, p220_1, u5ehi1]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h1, hlam, p220_1]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h4, hlam, p220_1]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [hlam, p220_0]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h7, hlam, p220_1]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h163, hlam, p220_1]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h2, hlam, p220_0]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h5, hlam, p220_0]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h1, h218, h7, hc13, hc45, hlam, hphi, ht34, p220_1]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [hlam, p220_0]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h165, hlam, p220_0]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h3, hlam, p220_0]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h6, hlam, p220_1]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h1, h163, hc13, hlam, hphi, p220_1, u3elo4]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [h163, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p220_1, u3elo4]
                            · have p220_0 := h220c.1
                              have p220_1 := h220c.2.1
                              have p220_2 := h220c.2.2.1
                              have p220_3 := h220c.2.2.2
                              linarith only [hlam, p220_0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h272 | h272
              · rcases m.htr 0 3 5 (by decide) (by decide) with h273 | h273
                · linarith only [h273, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h275 | h275
                  · linarith only [h272, h273, h275, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                      · linarith only [h2, h275, h278, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h281 | h281
                          · linarith only [h275, h280, h281, h4, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h0bigk with h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h272, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p283_1]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              rcases p283_3 (m.d 0 1) (by simp) with h287 | h287
                              · rcases p283_3 (m.d 0 2) (by simp) with h288 | h288
                                · linarith only [h0, h288, hlam]
                                · linarith only [h288, h5, hlam]
                              · linarith only [h2, h287, hlam]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h280, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p283_1]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h0, hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h1, h273, h277, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p283_1, u3elo4]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h2, h273, h277, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p283_1, u3elo4]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h6, hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h1, hlam, p283_1]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h4, hlam, p283_1]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h2, h277, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p283_1, u3elo0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h273, hlam, p283_1]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h2, hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h5, hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h272, hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h275, hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h3, hlam, p283_0]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h273, hc02, hlam, hphi, ht23, p283_1, u3elo4]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h273, hc03, hlam, hphi, p283_1, u3elo4]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [h2, h273, h277, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p283_1, u3elo4]
                            · have p283_0 := h283c.1
                              have p283_1 := h283c.2.1
                              have p283_2 := h283c.2.2.1
                              have p283_3 := h283c.2.2.2
                              linarith only [hlam, p283_0]
                        · linarith only [h1, h277, h280, hc23, hlam, hphi, u3elo0]
                    · linarith only [h272, h273, h277, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h315 | h315
                · linarith only [h272, h315, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h317 | h317
                  · linarith only [h317, h5, h6, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                    · linarith only [h272, h319, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                      · linarith only [h2, h317, h321, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h323 | h323
                        · linarith only [h1, h272, h323, hc13, hlam, hphi, u3elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h325 | h325
                          · linarith only [h317, h325, h4, h6, hc23, hlam, hphi, u3elo3]
                          · rcases h0bigk with h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [hlam, p327_0]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h323, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              rcases p327_3 (m.d 0 1) (by simp) with h330 | h330
                              · rcases p327_3 (m.d 0 2) (by simp) with h331 | h331
                                · linarith only [h0, h331, hlam]
                                · linarith only [h331, h4, hlam]
                              · linarith only [h1, h330, hlam]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              rcases p327_3 (m.d 0 1) (by simp) with h335 | h335
                              · rcases p327_3 (m.d 0 2) (by simp) with h336 | h336
                                · linarith only [h0, h336, hlam]
                                · linarith only [h336, h5, hlam]
                              · linarith only [h2, h335, hlam]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h323, h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h0, hlam, p327_0]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [hlam, p327_0]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h1, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p327_1]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h1, h272, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p327_1]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h6, hlam, p327_0]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h1, hlam, p327_1]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h4, hlam, p327_1]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [hlam, p327_0]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h272, hlam, p327_1]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h315, hlam, p327_1]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h2, hlam, p327_0]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h5, hlam, p327_0]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h1, h5, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p327_1]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [hlam, p327_0]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h317, hlam, p327_0]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h3, hlam, p327_0]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h1, h315, hc13, hlam, hphi, p327_1, u3elo4]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [h315, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p327_1, u3elo4]
                            · have p327_0 := h327c.1
                              have p327_1 := h327c.2.1
                              have p327_2 := h327c.2.2.1
                              have p327_3 := h327c.2.2.2
                              linarith only [hlam, p327_0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h361 | h361
            · rcases m.htr 0 3 4 (by decide) (by decide) with h362 | h362
              · linarith only [h362, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h364 | h364
                · linarith only [h362, h364, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h366 | h366
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h367 | h367
                    · linarith only [h362, h367, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h369 | h369
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h370 | h370
                        · linarith only [h361, h362, h370, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                        · linarith only [h361, h370, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                      · linarith only [h362, h366, h367, h369, hc13, hlam, hphi, u3elo3]
                  · linarith only [h361, h366, h5, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h375 | h375
              · linarith only [h375, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h377 | h377
                · linarith only [h375, h377, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h379 | h379
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h380 | h380
                    · linarith only [h375, h380, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h382 | h382
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h383 | h383
                        · linarith only [h361, h375, h379, h383, h4, hlam]
                        · linarith only [h383, h4, h5, hc23, hlam, hphi, u3elo3]
                      · linarith only [h375, h379, h380, h382, hc13, hlam, hphi, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h387 | h387
                    · linarith only [h375, h387, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h389 | h389
                      · linarith only [h2, h379, h389, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h391 | h391
                        · linarith only [h375, h391, h4, h5, hlam]
                        · linarith only [h391, h4, h5, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h394 | h394
          · rcases m.htr 0 2 5 (by decide) (by decide) with h395 | h395
            · linarith only [h395, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h397 | h397
              · rcases m.htr 0 3 5 (by decide) (by decide) with h398 | h398
                · rcases m.htr 0 4 5 (by decide) (by decide) with h399 | h399
                  · linarith only [h394, h399, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h402 | h402
                      · linarith only [h2, h399, h402, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h405 | h405
                          · linarith only [h395, h397, h399, h4, h405, hc02, hlam, hphi, ht23, u3elo2]
                          · rcases h0bigk with h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h394, h404, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p407_1]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h394, h4, h404, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p407_1]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              rcases p407_3 (m.d 0 1) (by simp) with h411 | h411
                              · rcases p407_3 (m.d 0 2) (by simp) with h412 | h412
                                · linarith only [h0, h412, hlam]
                                · linarith only [h394, h412, hlam]
                              · linarith only [h2, h411, hlam]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h394, h395, h404, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p407_1]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h0, hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h4, hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h395, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p407_1]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h395, hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h1, hlam, p407_1]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [hc02, hlam, hphi, ht23, p407_1, u3elo0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h394, h4, h404, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p407_1, u3elo2]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p407_1, u3elo2, u5ehi0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h2, hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h394, hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h397, hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h399, hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h3, hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h3, h394, h404, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p407_1]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h398, hlam, p407_0]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [h394, h398, h4, h404, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p407_1, u3elo2]
                            · have p407_0 := h407c.1
                              have p407_1 := h407c.2.1
                              have p407_2 := h407c.2.2.1
                              have p407_3 := h407c.2.2.2
                              linarith only [hlam, p407_0]
                        · linarith only [h4, h404, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h394, h397, h4, h401, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h439 | h439
                  · linarith only [h394, h398, h4, h439, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h441 | h441
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h442 | h442
                      · linarith only [h1, h398, h439, h441, h442, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h444 | h444
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h445 | h445
                          · linarith only [h395, h397, h398, h439, h445, hc02, hlam, hphi, ht23, u3elo4]
                          · rcases h0bigk with h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h394, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p447_1]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h394, h4, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p447_1]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              rcases p447_3 (m.d 0 1) (by simp) with h451 | h451
                              · rcases p447_3 (m.d 0 2) (by simp) with h452 | h452
                                · linarith only [h0, h452, hlam]
                                · linarith only [h394, h452, hlam]
                              · linarith only [h2, h451, hlam]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h394, h398, h4, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p447_1]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h0, hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h4, hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h2, h398, h4, h441, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p447_1, u3elo4]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h395, hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h1, hlam, p447_1]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h398, hc02, hlam, hphi, ht23, p447_1, u3elo4]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h2, h398, h441, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p447_1, u3elo4]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h398, hlam, p447_1]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h2, hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h394, hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h397, hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h439, hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h3, hlam, p447_0]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h394, h395, h444, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p447_1]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h398, hc03, hlam, hphi, p447_1, u3elo4]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [h2, h398, h441, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p447_1, u3elo4]
                            · have p447_0 := h447c.1
                              have p447_1 := h447c.2.1
                              have p447_2 := h447c.2.2.1
                              have p447_3 := h447c.2.2.2
                              linarith only [hlam, p447_0]
                        · linarith only [h441, h444, hc23, hlam, hphi, u3elo1]
                    · linarith only [h397, h398, h441, hc13, hlam, hphi, u3elo4]
              · linarith only [h394, h397, h4, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h480 | h480
            · linarith only [h4, h480, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h482 | h482
              · rcases m.htr 0 3 5 (by decide) (by decide) with h483 | h483
                · rcases m.htr 0 4 5 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h485 | h485
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h486 | h486
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h487 | h487
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h488 | h488
                          · linarith only [h482, h488, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                          · rcases h0bigk with h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              rcases p490_3 (m.d 0 1) (by simp) with h492 | h492
                              · rcases p490_3 (m.d 0 2) (by simp) with h493 | h493
                                · linarith only [h0, h493, hlam]
                                · rcases p490_3 (m.d 0 3) (by simp) with h495 | h495
                                  · linarith only [h1, h495, hlam]
                                  · linarith only [h4, h495, hlam]
                              · linarith only [h0, h492, hlam]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h482, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h2, h486, h488, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hc01, hlam, hphi, ht0b, ht5b, p490_1, u5ehi0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h0, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h4, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h394, hlam, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h480, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h1, hlam, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, p490_1, u3elo0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h2, h4, h486, h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p490_1, u3elo2]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h3, h4, h486, h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p490_1, u3elo2]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h2, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h0, h394, hc12, hc24, hlam, hphi, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h482, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h3, h4, h482, h486, h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p490_1, u3elo2]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h3, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h0, h480, hc12, hc25, hlam, hphi, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h483, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h484, hlam, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, p490_0]
                        · linarith only [h2, h4, h482, h486, h487, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h524 | h524
                          · linarith only [h485, h486, h524, hlam]
                          · rcases h0bigk with h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              rcases p526_3 (m.d 0 1) (by simp) with h528 | h528
                              · rcases p526_3 (m.d 0 2) (by simp) with h529 | h529
                                · linarith only [h0, h529, hlam]
                                · rcases p526_3 (m.d 0 3) (by simp) with h531 | h531
                                  · linarith only [h1, h531, hlam]
                                  · linarith only [h4, h531, hlam]
                              · linarith only [h0, h528, hlam]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h482, h484, h485, h486, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p526_1]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h484, h485, h486, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p526_1]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [hc01, hlam, hphi, ht0b, ht5b, p526_1, u5ehi0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h0, hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h4, hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h394, hlam, p526_1]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h480, hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h1, hlam, p526_1]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p526_1]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h4, h484, h485, h486, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p526_1, u3elo2]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p526_1, u3elo2, u5ehi1]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h2, hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h0, h394, hc12, hc24, hlam, hphi, p526_1]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h482, hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h3, h4, h482, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p526_1, u3elo2, u5ehi1]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h3, hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h0, h480, hc12, hc25, hlam, hphi, p526_1]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h483, hlam, p526_0]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [h484, hlam, p526_1]
                            · have p526_0 := h526c.1
                              have p526_1 := h526c.2.1
                              have p526_2 := h526c.2.2.1
                              have p526_3 := h526c.2.2.2
                              linarith only [hlam, p526_0]
                        · linarith only [h2, h4, h482, h485, h523, hlam]
                    · linarith only [h482, h485, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h560 | h560
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h561 | h561
                      · linarith only [h2, h484, h561, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h563 | h563
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h564 | h564
                          · linarith only [h0, h394, h484, h564, hc12, hlam, hphi, ht23, u3elo3]
                          · rcases h0bigk with h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              rcases p566_3 (m.d 0 1) (by simp) with h568 | h568
                              · rcases p566_3 (m.d 0 2) (by simp) with h569 | h569
                                · linarith only [h0, h569, hlam]
                                · rcases p566_3 (m.d 0 3) (by simp) with h571 | h571
                                  · linarith only [h1, h571, hlam]
                                  · linarith only [h4, h571, hlam]
                              · linarith only [h0, h568, hlam]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h1, h560, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p566_1]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              rcases p566_3 (m.d 0 1) (by simp) with h576 | h576
                              · rcases p566_3 (m.d 0 2) (by simp) with h577 | h577
                                · linarith only [h0, h577, hlam]
                                · rcases p566_3 (m.d 0 3) (by simp) with h579 | h579
                                  · linarith only [h1, h579, hlam]
                                  · linarith only [h482, h579, hlam]
                              · linarith only [h2, h576, hlam]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p566_1, u5ehi1]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h0, hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h4, hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h394, hlam, p566_1]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h480, hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h1, hlam, p566_1]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, p566_1, u3elo0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h0, h394, h4, hc12, hlam, hphi, ht23, p566_1, u3elo2]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p566_1, u3elo2, u5ehi1]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h2, hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h0, h484, hc12, hc45, hlam, hphi, ht23, ht34, p566_1]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h482, hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h484, hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h3, hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h0, h480, hc12, hc25, hlam, hphi, p566_1]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h483, hlam, p566_0]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [h4, h483, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p566_1, u3elo2]
                            · have p566_0 := h566c.1
                              have p566_1 := h566c.2.1
                              have p566_2 := h566c.2.2.1
                              have p566_3 := h566c.2.2.2
                              linarith only [hlam, p566_0]
                        · linarith only [h4, h560, h563, hc03, hlam, hphi, u3elo1]
                    · linarith only [h482, h560, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h606 | h606
                  · linarith only [h482, h483, h606, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h608 | h608
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h609 | h609
                      · linarith only [h1, h483, h606, h608, h609, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h611 | h611
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h612 | h612
                          · linarith only [h0, h394, h606, h612, hc12, hlam, hphi, ht23, u3elo3]
                          · rcases h0bigk with h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              rcases p614_3 (m.d 0 1) (by simp) with h616 | h616
                              · rcases p614_3 (m.d 0 2) (by simp) with h617 | h617
                                · linarith only [h0, h617, hlam]
                                · rcases p614_3 (m.d 0 3) (by simp) with h619 | h619
                                  · linarith only [h1, h619, hlam]
                                  · linarith only [h4, h619, hlam]
                              · linarith only [h0, h616, hlam]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h1, h608, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p614_1]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              rcases p614_3 (m.d 0 1) (by simp) with h624 | h624
                              · rcases p614_3 (m.d 0 2) (by simp) with h625 | h625
                                · linarith only [h0, h625, hlam]
                                · rcases p614_3 (m.d 0 3) (by simp) with h627 | h627
                                  · linarith only [h1, h627, hlam]
                                  · linarith only [h482, h627, hlam]
                              · linarith only [h2, h624, hlam]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h1, h483, h608, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p614_1]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h0, hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h4, hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h394, hlam, p614_1]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h480, hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h1, hlam, p614_1]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h0, h483, hc12, hlam, hphi, ht23, p614_1, u3elo4]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h483, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p614_1, u3elo4]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h483, hlam, p614_1]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h2, hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h0, h394, hc12, hc24, hlam, hphi, p614_1]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h482, hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h606, hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h3, hlam, p614_0]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h0, h480, hc12, hc25, hlam, hphi, p614_1]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h483, hc03, hlam, hphi, p614_1, u3elo4]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [h483, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p614_1, u3elo4]
                            · have p614_0 := h614c.1
                              have p614_1 := h614c.2.1
                              have p614_2 := h614c.2.2.1
                              have p614_3 := h614c.2.2.2
                              linarith only [hlam, p614_0]
                        · linarith only [h1, h608, h611, hc23, hlam, hphi, u3elo0]
                    · linarith only [h482, h483, h608, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h654 | h654
                · linarith only [h482, h654, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h656 | h656
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h657 | h657
                    · linarith only [h482, h657, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h659 | h659
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h660 | h660
                        · linarith only [h482, h660, hc03, hlam, hphi, u3elo2]
                        · linarith only [h0, h4, h660, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h482, h656, h657, h659, hc13, hlam, hphi, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h664 | h664
                    · linarith only [h1, h482, h664, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h666 | h666
                      · linarith only [h2, h656, h666, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                        · linarith only [h0, h4, h482, h668, hc12, hlam, hphi, ht23, u3elo2]
                        · linarith only [h0, h4, h668, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h671 | h671
        · rcases m.htr 0 2 4 (by decide) (by decide) with h672 | h672
          · rcases m.htr 0 2 5 (by decide) (by decide) with h673 | h673
            · linarith only [h0, h3, h673, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h675 | h675
              · rcases m.htr 0 3 5 (by decide) (by decide) with h676 | h676
                · linarith only [h1, h3, h676, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h678 | h678
                  · linarith only [h675, h676, h678, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h680 | h680
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h681 | h681
                      · linarith only [h0, h3, h678, h680, h681, hc12, hlam, hphi, ht23, u3elo1]
                      · linarith only [h1, h3, h680, h681, hc34, hc45, hlam, hphi]
                    · linarith only [h675, h676, h680, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h685 | h685
                · linarith only [h675, h685, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h687 | h687
                  · linarith only [h2, h3, h687, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h689 | h689
                    · linarith only [h675, h689, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h691 | h691
                      · linarith only [h2, h3, h687, h691, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h693 | h693
                        · linarith only [h1, h675, h693, hc13, hlam, hphi, u3elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h695 | h695
                          · linarith only [h3, h691, h695, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · rcases h0bigk with h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [hlam, p697_0]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h672, h693, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p697_1]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h1, h3, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p697_1]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h1, h3, h675, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p697_1]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h3, hlam, p697_1]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h0, hlam, p697_0]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [hlam, p697_0]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h1, h673, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p697_1]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h0, h1, h3, h675, h685, hc13, hlam, hphi, p697_1, u3elo4]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h673, hlam, p697_0]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h1, hlam, p697_1]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h671, hlam, p697_1]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [hlam, p697_0]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h675, hlam, p697_1]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h685, hlam, p697_1]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h2, hlam, p697_0]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h672, hlam, p697_0]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h1, h2, h3, h685, hc13, hlam, hphi, p697_1, u3elo4]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [hlam, p697_0]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h687, hlam, p697_0]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h685, hc01, hlam, hphi, ht12, ht23, p697_1, u3elo4]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h672, h685, h693, hc23, hlam, hphi, p697_1, u3elo4]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h1, h685, hc13, hlam, hphi, p697_1, u3elo4]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [h685, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p697_1, u3elo4]
                            · have p697_0 := h697c.1
                              have p697_1 := h697c.2.1
                              have p697_2 := h697c.2.2.1
                              have p697_3 := h697c.2.2.2
                              linarith only [hlam, p697_0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h723 | h723
            · linarith only [h2, h3, h672, h723, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h725 | h725
              · linarith only [h671, h672, h725, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h727 | h727
                · linarith only [h725, h727, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h729 | h729
                  · linarith only [h2, h3, h729, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h731 | h731
                    · linarith only [h725, h731, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h733 | h733
                      · linarith only [h2, h3, h727, h729, h733, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h735 | h735
                        · linarith only [h671, h672, h725, h735, hlam]
                        · linarith only [h671, h672, h735, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h738 | h738
          · rcases m.htr 0 2 5 (by decide) (by decide) with h739 | h739
            · linarith only [h671, h739, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h741 | h741
              · rcases m.htr 0 3 5 (by decide) (by decide) with h742 | h742
                · linarith only [h1, h3, h742, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h744 | h744
                  · linarith only [h671, h738, h742, h744, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h746 | h746
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h747 | h747
                      · linarith only [h2, h3, h744, h747, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1, h3, h746, h747, hc34, hc45, hlam, hphi]
                    · linarith only [h741, h742, h746, hc13, hlam, hphi, u3elo4]
              · linarith only [h671, h738, h741, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h752 | h752
            · linarith only [h671, h752, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h754 | h754
              · rcases m.htr 0 3 5 (by decide) (by decide) with h755 | h755
                · linarith only [h1, h3, h755, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h757 | h757
                  · linarith only [h754, h755, h757, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h759 | h759
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h760 | h760
                      · linarith only [h2, h3, h738, h757, h760, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h1, h3, h759, h760, hc34, hc45, hlam, hphi]
                    · linarith only [h754, h755, h759, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h764 | h764
                · linarith only [h754, h764, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h766 | h766
                  · linarith only [h2, h3, h766, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h768 | h768
                    · linarith only [h754, h768, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h770 | h770
                      · linarith only [h2, h3, h766, h770, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h772 | h772
                        · linarith only [h0, h671, h754, h772, hc12, hlam, hphi, ht23, u3elo2]
                        · linarith only [h0, h671, h772, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h775 | h775
      · rcases m.htr 0 2 3 (by decide) (by decide) with h776 | h776
        · rcases m.htr 0 2 4 (by decide) (by decide) with h777 | h777
          · linarith only [h0, h2, h777, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h779 | h779
            · rcases m.htr 0 3 4 (by decide) (by decide) with h780 | h780
              · linarith only [h1, h2, h780, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h782 | h782
                · linarith only [h780, h782, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h784 | h784
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h785 | h785
                    · linarith only [h780, h785, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2, h779, h785, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                  · linarith only [h0, h2, h779, h784, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h789 | h789
              · linarith only [h1, h2, h789, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h791 | h791
                · linarith only [h789, h791, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h793 | h793
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h794 | h794
                    · linarith only [h789, h794, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2, h794, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h2, h775, h793, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h798 | h798
          · linarith only [h0, h2, h798, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h800 | h800
            · linarith only [h776, h800, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h802 | h802
              · linarith only [h1, h2, h802, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h804 | h804
                · linarith only [h802, h804, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h806 | h806
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h807 | h807
                    · linarith only [h776, h802, h807, hc02, hlam, hphi, ht23, u3elo1]
                    · linarith only [h2, h775, h807, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi1]
                  · linarith only [h2, h775, h806, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h811 | h811
        · rcases m.htr 0 2 4 (by decide) (by decide) with h812 | h812
          · linarith only [h0, h2, h812, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h814 | h814
            · linarith only [h0, h775, h814, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h816 | h816
              · linarith only [h0, h2, h811, h816, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h818 | h818
                · linarith only [h816, h818, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h820 | h820
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h821 | h821
                    · linarith only [h1, h2, h816, h821, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h821, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h824 | h824
                    · linarith only [h1, h2, h820, h824, hc34, hc45, hlam, hphi]
                    · linarith only [h1, h2, h824, hc13, hlam, hphi, u3elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h827 | h827
          · linarith only [h0, h2, h827, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h829 | h829
            · linarith only [h811, h829, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h831 | h831
              · linarith only [h1, h2, h831, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h833 | h833
                · linarith only [h831, h833, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h835 | h835
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h836 | h836
                    · linarith only [h811, h831, h836, hc02, hlam, hphi, ht23, u3elo1]
                    · linarith only [h0, h2, h836, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h839 | h839
                    · linarith only [h1, h2, h811, h831, h839, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h839, hc12, hlam, hphi, ht23, u3elo3]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
