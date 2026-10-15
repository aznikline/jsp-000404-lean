import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_13_15_H_I_L_0_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
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
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                        · rcases h0bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h1, h10, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h12, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            rcases p13_3 (m.d 0 1) (by simp) with h18 | h18
                            · rcases p13_3 (m.d 0 2) (by simp) with h19 | h19
                              · linarith only [h0, h19, hlam]
                              · linarith only [h19, h6, hlam]
                            · linarith only [h18, h3, hlam]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h0, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h1, h10, h12, hc02, hc45, hlam, hphi, ht0b, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h0, h10, h12, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            rcases p13_3 (m.d 0 1) (by simp) with h27 | h27
                            · rcases p13_3 (m.d 0 2) (by simp) with h28 | h28
                              · rcases p13_3 (m.d 0 3) (by simp) with h29 | h29
                                · linarith only [h29, h4, hlam]
                                · linarith only [h29, h8, hlam]
                              · linarith only [h28, h6, hlam]
                            · linarith only [h27, h3, hlam]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h1, hlam, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h4, hlam, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h10, h12, h2, hc03, hc45, hlam, hphi, ht0b, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h2, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h5, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h7, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h3, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h3, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h6, hlam, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h8, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h9, hlam, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
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
                            linarith only [h11, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h1, h10, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h0, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h12, h8, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h0, h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h0, h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h1, hlam, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h4, hlam, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p49_1, u3elo0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h12, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p49_1, u3elo0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h2, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h5, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h7, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h12, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h3, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h6, hlam, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h8, hlam, p49_0]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [h9, hlam, p49_1]
                          · have p49_0 := h49c.1
                            have p49_1 := h49c.2.1
                            have p49_2 := h49c.2.2.1
                            have p49_3 := h49c.2.2.2
                            linarith only [hlam, p49_0]
                      · linarith only [h10, h11, hc23, hlam, hphi, u3elo1]
                    · linarith only [h10, h7, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                        · linarith only [h77, h79, h9, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · rcases h0bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h4, h78, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p81_1]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            rcases p81_3 (m.d 0 1) (by simp) with h85 | h85
                            · rcases p81_3 (m.d 0 2) (by simp) with h86 | h86
                              · linarith only [h0, h86, hlam]
                              · linarith only [h5, h86, hlam]
                            · linarith only [h2, h85, hlam]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            rcases p81_3 (m.d 0 1) (by simp) with h90 | h90
                            · rcases p81_3 (m.d 0 2) (by simp) with h91 | h91
                              · linarith only [h0, h91, hlam]
                              · linarith only [h6, h91, hlam]
                            · linarith only [h3, h90, hlam]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h0, hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h4, h78, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p81_1]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            rcases p81_3 (m.d 0 1) (by simp) with h98 | h98
                            · rcases p81_3 (m.d 0 2) (by simp) with h99 | h99
                              · rcases p81_3 (m.d 0 3) (by simp) with h100 | h100
                                · linarith only [h100, h4, hlam]
                                · linarith only [h100, h7, hlam]
                              · linarith only [h5, h99, hlam]
                            · linarith only [h2, h98, hlam]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            rcases p81_3 (m.d 0 1) (by simp) with h105 | h105
                            · rcases p81_3 (m.d 0 2) (by simp) with h106 | h106
                              · rcases p81_3 (m.d 0 3) (by simp) with h107 | h107
                                · linarith only [h107, h4, hlam]
                                · linarith only [h107, h8, hlam]
                              · linarith only [h106, h6, hlam]
                            · linarith only [h105, h3, hlam]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h1, hlam, p81_1]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h4, hlam, p81_1]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p81_1, u3elo0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p81_1, u3elo0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h2, hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h5, hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h7, hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h9, hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h3, hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h6, hlam, p81_1]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h8, hlam, p81_0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [h2, h77, hc34, hlam, hphi, ht45, p81_1, u5elo0]
                          · have p81_0 := h81c.1
                            have p81_1 := h81c.2.1
                            have p81_2 := h81c.2.2.1
                            have p81_3 := h81c.2.2.2
                            linarith only [hlam, p81_0]
                      · linarith only [h7, h78, hc23, hlam, hphi, u3elo0]
                    · linarith only [h7, h77, h9, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h130 | h130
                · rcases m.htr 0 4 5 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                    · linarith only [h130, h132, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                      · linarith only [h130, h134, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h136 | h136
                        · rcases h0bigk with h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h130, h136, hc01, hc45, hlam, hphi, ht0b, ht5b, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h130, h136, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            rcases p137_3 (m.d 0 1) (by simp) with h142 | h142
                            · rcases p137_3 (m.d 0 2) (by simp) with h143 | h143
                              · linarith only [h0, h143, hlam]
                              · linarith only [h143, h6, hlam]
                            · linarith only [h142, h3, hlam]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h0, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h130, h136, hc02, hc45, hlam, hphi, ht0b, ht5b, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h0, h130, h136, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            rcases p137_3 (m.d 0 1) (by simp) with h151 | h151
                            · rcases p137_3 (m.d 0 2) (by simp) with h152 | h152
                              · rcases p137_3 (m.d 0 3) (by simp) with h153 | h153
                                · linarith only [h153, h4, hlam]
                                · linarith only [h130, h153, hlam]
                              · linarith only [h152, h6, hlam]
                            · linarith only [h151, h3, hlam]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h1, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h4, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h7, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h6, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p137_1, u3elo3]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h2, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h5, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h1, h7, hc13, hlam, hphi, p137_1, u3elo3]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h130, h136, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p137_1, u3elo3]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h3, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h6, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h130, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h131, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                        · linarith only [h136, h7, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h130, h131, h7, hc35, hlam, hphi, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h176 | h176
                    · linarith only [h176, h7, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                      · linarith only [h1, h178, h7, hc13, hlam, hphi, u3elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h180 | h180
                        · rcases h0bigk with h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            rcases p181_3 (m.d 0 1) (by simp) with h184 | h184
                            · rcases p181_3 (m.d 0 2) (by simp) with h185 | h185
                              · linarith only [h0, h185, hlam]
                              · linarith only [h185, h4, hlam]
                            · linarith only [h1, h184, hlam]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h175, hc01, hc45, hlam, hphi, ht0b, ht5b, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            rcases p181_3 (m.d 0 1) (by simp) with h190 | h190
                            · rcases p181_3 (m.d 0 2) (by simp) with h191 | h191
                              · linarith only [h0, h191, hlam]
                              · linarith only [h191, h6, hlam]
                            · linarith only [h190, h3, hlam]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h0, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            rcases p181_3 (m.d 0 1) (by simp) with h197 | h197
                            · rcases p181_3 (m.d 0 2) (by simp) with h198 | h198
                              · rcases p181_3 (m.d 0 3) (by simp) with h199 | h199
                                · linarith only [h199, h4, hlam]
                                · rcases p181_3 (m.d 0 4) (by simp) with h201 | h201
                                  · linarith only [h201, h5, hlam]
                                  · linarith only [h201, h7, hlam]
                              · linarith only [h198, h4, hlam]
                            · linarith only [h1, h197, hlam]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h175, hc02, hc45, hlam, hphi, ht0b, ht5b, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            rcases p181_3 (m.d 0 1) (by simp) with h207 | h207
                            · rcases p181_3 (m.d 0 2) (by simp) with h208 | h208
                              · rcases p181_3 (m.d 0 3) (by simp) with h209 | h209
                                · linarith only [h209, h4, hlam]
                                · rcases p181_3 (m.d 0 4) (by simp) with h211 | h211
                                  · linarith only [h211, h5, hlam]
                                  · linarith only [h175, h211, hlam]
                              · linarith only [h208, h6, hlam]
                            · linarith only [h207, h3, hlam]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h1, hlam, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h4, hlam, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h7, hlam, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h130, hlam, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h2, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h5, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h1, h7, hc13, hlam, hphi, p181_1, u3elo3]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h1, h130, h7, hc13, hlam, hphi, p181_1, u3elo3]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h3, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h6, hlam, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h1, hc13, hlam, hphi, ht34, ht45, p181_1, u5elo0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h175, hlam, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hlam, p181_0]
                        · linarith only [h1, h180, h7, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                    · linarith only [h1, h232, h7, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                      · linarith only [h1, h234, h7, hc13, hlam, hphi, u3elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h236 | h236
                        · linarith only [h1, h175, h236, h7, hc13, hlam, hphi, u3elo3]
                        · linarith only [h1, h236, h7, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h240 | h240
            · rcases m.htr 0 3 4 (by decide) (by decide) with h241 | h241
              · linarith only [h241, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h243 | h243
                · rcases m.htr 0 4 5 (by decide) (by decide) with h244 | h244
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h245 | h245
                    · linarith only [h241, h245, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                      · linarith only [h241, h243, h247, h4, hc02, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h247, h4, h5, hc23, hlam, hphi, u3elo3]
                  · linarith only [h244, h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h251 | h251
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h252 | h252
                    · linarith only [h1, h243, h252, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
                      · linarith only [h1, h241, h254, h4, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h254, h4, h5, hc23, hlam, hphi, u3elo3]
                  · linarith only [h251, h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h240, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h259 | h259
          · rcases m.htr 0 2 5 (by decide) (by decide) with h260 | h260
            · rcases m.htr 0 3 4 (by decide) (by decide) with h261 | h261
              · rcases m.htr 0 3 5 (by decide) (by decide) with h262 | h262
                · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h265 | h265
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h266 | h266
                        · linarith only [h259, h265, h266, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · linarith only [h259, h263, h266, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h259, h264, h265, h4, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h261, h264, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h271 | h271
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h273 | h273
                        · linarith only [h259, h263, h272, h273, h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · rcases h0bigk with h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h259, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p275_1]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h1, h271, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p275_1]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            rcases p275_3 (m.d 0 1) (by simp) with h279 | h279
                            · rcases p275_3 (m.d 0 2) (by simp) with h280 | h280
                              · linarith only [h0, h280, hlam]
                              · linarith only [h259, h280, hlam]
                            · linarith only [h2, h279, hlam]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            rcases p275_3 (m.d 0 1) (by simp) with h284 | h284
                            · rcases p275_3 (m.d 0 2) (by simp) with h285 | h285
                              · linarith only [h0, h285, hlam]
                              · linarith only [h260, h285, hlam]
                            · linarith only [h284, h3, hlam]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h0, hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h4, hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h259, h272, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p275_1, u3elo2]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h259, h263, h272, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p275_1, u3elo2]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h1, hlam, p275_1]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h260, hc03, hc25, hlam, hphi, ht0b, ht5b, p275_1]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h259, h272, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p275_1, u3elo2]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h259, h263, h272, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p275_1, u3elo2]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h2, hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h259, hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h261, hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h263, hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h3, hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h260, hlam, p275_1]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h262, hlam, p275_0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [h259, h272, hc34, hlam, hphi, ht45, p275_1, u5elo0]
                          · have p275_0 := h275c.1
                            have p275_1 := h275c.2.1
                            have p275_2 := h275c.2.2.1
                            have p275_3 := h275c.2.2.2
                            linarith only [hlam, p275_0]
                      · linarith only [h271, h272, h4, hc03, hlam, hphi, u3elo1]
                    · linarith only [h261, h263, h271, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h259, h262, h4, hc24, hlam, hphi, ht45, u5elo3]
              · linarith only [h259, h261, h4, hlam]
            · linarith only [h259, h260, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h314 | h314
            · rcases m.htr 0 3 4 (by decide) (by decide) with h315 | h315
              · rcases m.htr 0 3 5 (by decide) (by decide) with h316 | h316
                · rcases m.htr 0 4 5 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h320 | h320
                        · rcases h0bigk with h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [hlam, p321_0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h314, hc01, hc25, hlam, hphi, ht0b, ht5b, p321_1]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h1, h318, h320, hc01, hc45, hlam, hphi, ht0b, ht5b, p321_1]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h2, h318, h320, hc01, hc45, hlam, hphi, ht0b, ht5b, p321_1]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            rcases p321_3 (m.d 0 1) (by simp) with h326 | h326
                            · rcases p321_3 (m.d 0 2) (by simp) with h327 | h327
                              · linarith only [h0, h327, hlam]
                              · linarith only [h314, h327, hlam]
                            · linarith only [h3, h326, hlam]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h0, hlam, p321_0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [hlam, p321_0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h4, hlam, p321_0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h259, hlam, p321_1]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h259, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p321_1]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h1, hlam, p321_1]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, p321_1, u3elo0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [hlam, p321_0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h2, h318, h320, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p321_1, u3elo2]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h316, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p321_1, u3elo2]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h2, hlam, p321_0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h314, hc04, hc25, hlam, hphi, ht0b, ht5b, p321_1]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h315, hlam, p321_0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [hlam, p321_0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h315, h316, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p321_1, u3elo2]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h3, hlam, p321_0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h314, hlam, p321_1]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h316, hlam, p321_0]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [h317, hlam, p321_1]
                          · have p321_0 := h321c.1
                            have p321_1 := h321c.2.1
                            have p321_2 := h321c.2.2.1
                            have p321_3 := h321c.2.2.2
                            linarith only [hlam, p321_0]
                        · rcases h0bigk with h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [hlam, p351_0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h314, h317, h320, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p351_1]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h1, h318, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p351_1]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h317, h320, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p351_1]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h317, h320, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p351_1]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h0, hlam, p351_0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [hlam, p351_0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h4, hlam, p351_0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h259, hlam, p351_1]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h259, h317, h319, h320, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p351_1, u3elo2]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h1, hlam, p351_1]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, p351_1, u3elo0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [hlam, p351_0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h317, h320, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p351_1, u3elo2]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h317, h320, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p351_1, u3elo2]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h2, hlam, p351_0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h314, h317, h320, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p351_1]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h315, hlam, p351_0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [hlam, p351_0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h259, h317, h319, h320, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p351_1, u3elo2]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h3, hlam, p351_0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h314, hlam, p351_1]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h316, hlam, p351_0]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [h317, hlam, p351_1]
                          · have p351_0 := h351c.1
                            have p351_1 := h351c.2.1
                            have p351_2 := h351c.2.2.1
                            have p351_3 := h351c.2.2.2
                            linarith only [hlam, p351_0]
                      · linarith only [h318, h319, h4, hc03, hlam, hphi, u3elo1]
                    · linarith only [h315, h318, hc13, hlam, hphi, u3elo0]
                  · linarith only [h259, h314, h317, hc25, hlam, hphi, u5elo4]
                · linarith only [h315, h316, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h381 | h381
                · rcases m.htr 0 4 5 (by decide) (by decide) with h382 | h382
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h383 | h383
                    · linarith only [h314, h315, h383, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h385 | h385
                      · linarith only [h314, h315, h385, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h314, h385, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h314, h315, h382, h4, hc25, hlam, hphi, u5elo4]
                · linarith only [h314, h381, h4, hc25, hlam, hphi, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h390 | h390
              · rcases m.htr 0 3 5 (by decide) (by decide) with h391 | h391
                · rcases m.htr 0 4 5 (by decide) (by decide) with h392 | h392
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h393 | h393
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h395 | h395
                        · rcases h0bigk with h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            rcases p396_3 (m.d 0 1) (by simp) with h398 | h398
                            · rcases p396_3 (m.d 0 2) (by simp) with h399 | h399
                              · linarith only [h0, h399, hlam]
                              · rcases p396_3 (m.d 0 3) (by simp) with h401 | h401
                                · linarith only [h1, h401, hlam]
                                · linarith only [h4, h401, hlam]
                            · linarith only [h0, h398, hlam]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h1, h393, h395, hc01, hc45, hlam, hphi, ht0b, ht5b, p396_1]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h390, h395, hc01, hc45, hlam, hphi, ht0b, ht5b, p396_1]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            rcases p396_3 (m.d 0 1) (by simp) with h407 | h407
                            · rcases p396_3 (m.d 0 2) (by simp) with h408 | h408
                              · linarith only [h0, h408, hlam]
                              · rcases p396_3 (m.d 0 3) (by simp) with h410 | h410
                                · linarith only [h1, h410, hlam]
                                · linarith only [h391, h410, hlam]
                            · linarith only [h3, h407, hlam]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h0, hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h4, hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h259, hlam, p396_1]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h314, hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h1, hlam, p396_1]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht23, p396_1, u3elo0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h2, h393, h395, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p396_1, u3elo2]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h0, h314, h4, hc12, hlam, hphi, ht23, p396_1, u3elo2]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h2, hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h0, h259, h394, hc12, hlam, hphi, ht23, p396_1, u3elo2]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h390, hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h0, h259, h314, h394, hc12, hlam, hphi, ht23, p396_1, u3elo2]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h3, hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p396_1, u5elo0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h391, hlam, p396_0]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [h392, hlam, p396_1]
                          · have p396_0 := h396c.1
                            have p396_1 := h396c.2.1
                            have p396_2 := h396c.2.2.1
                            have p396_3 := h396c.2.2.2
                            linarith only [hlam, p396_0]
                        · rcases h0bigk with h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            rcases p434_3 (m.d 0 1) (by simp) with h436 | h436
                            · rcases p434_3 (m.d 0 2) (by simp) with h437 | h437
                              · linarith only [h0, h437, hlam]
                              · rcases p434_3 (m.d 0 3) (by simp) with h439 | h439
                                · linarith only [h1, h439, hlam]
                                · linarith only [h4, h439, hlam]
                            · linarith only [h0, h436, hlam]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h390, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h392, h395, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h392, h395, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h4, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h259, hlam, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h314, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h1, hlam, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht23, p434_1, u3elo0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h392, h395, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p434_1, u3elo2]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, h314, h4, hc12, hlam, hphi, ht23, p434_1, u3elo2]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h2, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, h259, hc12, hc24, hlam, hphi, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h390, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, h314, h390, h4, hc12, hlam, hphi, ht23, p434_1, u3elo2]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h3, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p434_1, u5elo0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h391, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h392, hlam, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                      · linarith only [h2, h390, h393, h394, h4, hlam]
                    · linarith only [h390, h393, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h468 | h468
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h469 | h469
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h470 | h470
                        · linarith only [h392, h468, h470, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · rcases h0bigk with h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            rcases p472_3 (m.d 0 1) (by simp) with h474 | h474
                            · rcases p472_3 (m.d 0 2) (by simp) with h475 | h475
                              · linarith only [h0, h475, hlam]
                              · rcases p472_3 (m.d 0 3) (by simp) with h477 | h477
                                · linarith only [h1, h477, hlam]
                                · linarith only [h4, h477, hlam]
                            · linarith only [h0, h474, hlam]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h390, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p472_1]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            rcases p472_3 (m.d 0 1) (by simp) with h482 | h482
                            · rcases p472_3 (m.d 0 2) (by simp) with h483 | h483
                              · linarith only [h0, h483, hlam]
                              · rcases p472_3 (m.d 0 3) (by simp) with h485 | h485
                                · linarith only [h1, h485, hlam]
                                · linarith only [h390, h485, hlam]
                            · linarith only [h2, h482, hlam]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            rcases p472_3 (m.d 0 1) (by simp) with h489 | h489
                            · rcases p472_3 (m.d 0 2) (by simp) with h490 | h490
                              · linarith only [h0, h490, hlam]
                              · rcases p472_3 (m.d 0 3) (by simp) with h492 | h492
                                · linarith only [h1, h492, hlam]
                                · linarith only [h391, h492, hlam]
                            · linarith only [h3, h489, hlam]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h0, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h4, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h259, hlam, p472_1]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h314, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h1, hlam, p472_1]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht23, p472_1, u3elo0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h0, h259, h4, hc12, hlam, hphi, ht23, p472_1, u3elo2]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h0, h259, h392, h4, hc12, hlam, hphi, ht23, p472_1, u3elo2]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h2, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h0, h392, hc12, hlam, hphi, ht23, ht34, ht45, p472_1, u5elo0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h390, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h392, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h3, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h0, h314, hc12, hlam, hphi, ht23, ht34, ht45, p472_1, u5elo2]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h391, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h314, hc04, hlam, hphi, ht45, p472_1, u5elo2]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [hlam, p472_0]
                      · linarith only [h0, h4, h469, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h390, h468, hc13, hlam, hphi, u3elo0]
                · linarith only [h390, h391, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h519 | h519
                · rcases m.htr 0 4 5 (by decide) (by decide) with h520 | h520
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h521 | h521
                    · linarith only [h390, h519, h521, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
                      · linarith only [h390, h519, h523, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h0, h4, h523, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h390, h519, h520, hc35, hlam, hphi, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h527 | h527
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h528 | h528
                    · linarith only [h1, h519, h528, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h530 | h530
                      · linarith only [h390, h530, hc03, hlam, hphi, u3elo2]
                      · linarith only [h0, h4, h530, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h533 | h533
                    · linarith only [h1, h390, h527, h533, hc34, hlam, hphi, ht45, u5elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h535 | h535
                      · linarith only [h0, h390, h4, h535, hc12, hlam, hphi, ht23, u3elo2]
                      · linarith only [h0, h4, h535, hc12, hlam, hphi, ht23, u3elo3]
      · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h539 | h539
      · rcases m.htr 0 2 3 (by decide) (by decide) with h540 | h540
        · rcases m.htr 0 2 4 (by decide) (by decide) with h541 | h541
          · linarith only [h0, h2, h541, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h543 | h543
            · rcases m.htr 0 3 4 (by decide) (by decide) with h544 | h544
              · linarith only [h1, h2, h544, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h546 | h546
                · rcases m.htr 0 4 5 (by decide) (by decide) with h547 | h547
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
                    · linarith only [h1, h2, h544, h548, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h548, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h0, h2, h547, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h552 | h552
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h553 | h553
                    · linarith only [h1, h546, h553, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h0, h2, h553, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h0, h2, h552, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h540, h543, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h558 | h558
          · linarith only [h0, h2, h540, h558, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h560 | h560
            · rcases m.htr 0 3 4 (by decide) (by decide) with h561 | h561
              · linarith only [h1, h2, h561, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h563 | h563
                · rcases m.htr 0 4 5 (by decide) (by decide) with h564 | h564
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h565 | h565
                    · linarith only [h540, h561, h565, hc02, hlam, hphi, ht23, u3elo1]
                    · linarith only [h0, h2, h565, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h0, h2, h564, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h540, h560, h563, hc25, hlam, hphi, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h570 | h570
              · linarith only [h1, h2, h570, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h572 | h572
                · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h574 | h574
                    · linarith only [h1, h2, h570, h574, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h574, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h0, h2, h573, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h578 | h578
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h579 | h579
                    · linarith only [h1, h572, h579, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h0, h2, h579, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h0, h2, h578, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
      · linarith only [h0, h539, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

theorem r1l7_20_13_15_H_I_L_0_L_0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h585 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h586 | h586
  · rcases m.htr 0 1 5 (by decide) (by decide) with h587 | h587
    · rcases m.htr 0 2 3 (by decide) (by decide) with h588 | h588
      · rcases m.htr 0 2 4 (by decide) (by decide) with h589 | h589
        · rcases m.htr 0 2 5 (by decide) (by decide) with h590 | h590
          · rcases m.htr 0 3 4 (by decide) (by decide) with h591 | h591
            · rcases m.htr 0 3 5 (by decide) (by decide) with h592 | h592
              · rcases m.htr 0 4 5 (by decide) (by decide) with h593 | h593
                · rcases m.htr 1 3 4 (by decide) (by decide) with h594 | h594
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h596 | h596
                      · linarith only [h0, h585, h594, h596, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases h0bigk with h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [hlam, p598_0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h0, hlam, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h587, hc02, hc15, hlam, hphi, ht0b, ht5b, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [hlam, p598_0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h0, h591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h0, h593, h596, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h0, h593, h596, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h585, hlam, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h588, hlam, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [hlam, p598_0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h593, h596, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p598_1, u3elo0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h593, h596, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p598_1, u3elo0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h586, hlam, p598_0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h589, hlam, p598_0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h591, hlam, p598_0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [hlam, p598_0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h593, h596, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h587, hlam, p598_0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h590, hlam, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h592, hlam, p598_0]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [h593, hlam, p598_1]
                        · have p598_0 := h598c.1
                          have p598_1 := h598c.2.1
                          have p598_2 := h598c.2.2.1
                          have p598_3 := h598c.2.2.2
                          linarith only [hlam, p598_0]
                    · linarith only [h594, h595, hc23, hlam, hphi, u3elo1]
                  · linarith only [h591, h594, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h626 | h626
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h627 | h627
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h628 | h628
                      · linarith only [h591, h593, h628, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · rcases h0bigk with h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [hlam, p630_0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h0, hlam, p630_1]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p630_1]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h0, h586, h626, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p630_1]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p630_1]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p630_1]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [hlam, p630_0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h0, h591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p630_1]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          rcases p630_3 (m.d 0 1) (by simp) with h639 | h639
                          · linarith only [h0, h639, hlam]
                          · linarith only [h586, h639, hlam]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          rcases p630_3 (m.d 0 1) (by simp) with h642 | h642
                          · linarith only [h0, h642, hlam]
                          · linarith only [h587, h642, hlam]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h585, hlam, p630_1]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h588, hlam, p630_1]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [hlam, p630_0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h586, h626, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p630_1, u3elo0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h586, h593, h626, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p630_1, u3elo0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h586, hlam, p630_0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h589, hlam, p630_0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h591, hlam, p630_0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [hlam, p630_0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h593, hlam, p630_0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h587, hlam, p630_0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h590, hlam, p630_1]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h592, hlam, p630_0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [h586, h626, hc34, hlam, hphi, ht45, p630_1, u5elo0]
                        · have p630_0 := h630c.1
                          have p630_1 := h630c.2.1
                          have p630_2 := h630c.2.2.1
                          have p630_3 := h630c.2.2.2
                          linarith only [hlam, p630_0]
                    · linarith only [h626, h627, hc23, hlam, hphi, u3elo1]
                  · linarith only [h591, h593, h626, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h591, h592, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h663 | h663
              · rcases m.htr 0 4 5 (by decide) (by decide) with h664 | h664
                · rcases m.htr 1 3 4 (by decide) (by decide) with h665 | h665
                  · linarith only [h585, h591, h663, h665, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h667 | h667
                    · linarith only [h591, h663, h667, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h669 | h669
                      · rcases h0bigk with h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h0, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h0, h663, h669, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h0, h591, h663, h669, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h0, h663, h669, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h0, h591, h663, h669, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          rcases p670_3 (m.d 0 1) (by simp) with h680 | h680
                          · linarith only [h0, h680, hlam]
                          · linarith only [h587, h680, hlam]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h585, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h588, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h591, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h591, h663, h669, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p670_1, u3elo3]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h586, hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h589, hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h0, h586, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h591, h663, h669, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p670_1, u3elo3]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h587, hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h590, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h663, hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h664, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [hlam, p670_0]
                      · linarith only [h588, h591, h669, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h591, h663, h664, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h700 | h700
                · rcases m.htr 1 3 4 (by decide) (by decide) with h701 | h701
                  · linarith only [h591, h701, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h703 | h703
                    · linarith only [h585, h591, h703, hc13, hlam, hphi, u3elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h705 | h705
                      · rcases h0bigk with h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [hlam, p706_0]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h0, hlam, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h0, h585, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h0, h700, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h0, h585, h663, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [hlam, p706_0]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          rcases p706_3 (m.d 0 1) (by simp) with h714 | h714
                          · linarith only [h0, h714, hlam]
                          · linarith only [h585, h714, hlam]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h0, h700, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          rcases p706_3 (m.d 0 1) (by simp) with h718 | h718
                          · linarith only [h0, h718, hlam]
                          · linarith only [h587, h718, hlam]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h585, hlam, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h588, hlam, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [hlam, p706_0]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h591, hlam, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h663, hlam, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h586, hlam, p706_0]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h589, hlam, p706_0]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h0, h585, h586, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [hlam, p706_0]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h585, h591, h663, hc13, hlam, hphi, p706_1, u3elo3]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h587, hlam, p706_0]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h590, hlam, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h585, hc13, hlam, hphi, ht34, ht45, p706_1, u5elo0]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [h700, hlam, p706_1]
                        · have p706_0 := h706c.1
                          have p706_1 := h706c.2.1
                          have p706_2 := h706c.2.2.1
                          have p706_3 := h706c.2.2.2
                          linarith only [hlam, p706_0]
                      · linarith only [h585, h591, h705, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h737 | h737
                  · linarith only [h585, h591, h737, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h739 | h739
                    · linarith only [h588, h591, h739, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h741 | h741
                      · linarith only [h585, h591, h700, h741, hc13, hlam, hphi, u3elo3]
                      · linarith only [h585, h591, h741, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h0, h585, h590, hc13, hlam, hphi, ht34, ht45, u5elo2]
        · linarith only [h0, h586, h589, hlam]
      · linarith only [h0, h585, h588, hc13, hlam, hphi, u3elo2]
    · linarith only [h585, h587, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h748 | h748
    · rcases m.htr 0 2 3 (by decide) (by decide) with h749 | h749
      · rcases m.htr 0 2 4 (by decide) (by decide) with h750 | h750
        · rcases m.htr 0 2 5 (by decide) (by decide) with h751 | h751
          · rcases m.htr 0 3 4 (by decide) (by decide) with h752 | h752
            · linarith only [h585, h586, h752, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h754 | h754
              · rcases m.htr 0 4 5 (by decide) (by decide) with h755 | h755
                · rcases m.htr 1 3 4 (by decide) (by decide) with h756 | h756
                  · linarith only [h585, h586, h752, h756, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h585, h586, h756, hc13, hlam, hphi, u3elo3]
                · linarith only [h585, h586, h755, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h760 | h760
                · rcases m.htr 1 3 4 (by decide) (by decide) with h761 | h761
                  · linarith only [h585, h754, h761, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h585, h586, h761, hc13, hlam, hphi, u3elo3]
                · linarith only [h585, h586, h760, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h0, h585, h751, hc13, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h766 | h766
          · rcases m.htr 0 3 4 (by decide) (by decide) with h767 | h767
            · linarith only [h0, h585, h750, h767, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h769 | h769
              · rcases m.htr 0 4 5 (by decide) (by decide) with h770 | h770
                · rcases m.htr 1 3 4 (by decide) (by decide) with h771 | h771
                  · linarith only [h585, h586, h767, h771, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h585, h586, h771, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h585, h750, h770, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h775 | h775
                · rcases m.htr 1 3 4 (by decide) (by decide) with h776 | h776
                  · linarith only [h585, h769, h776, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h585, h586, h776, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h585, h750, h775, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h0, h585, h766, hc13, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h0, h585, h749, hc13, hlam, hphi, u3elo2]
    · linarith only [h585, h748, hc13, hlam, hphi, ht34, ht45, u5elo1]

end R2N4
