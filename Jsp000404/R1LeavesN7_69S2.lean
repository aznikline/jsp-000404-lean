import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_25_L_0_L_R_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                            · linarith only [h1, h11, h14, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h1, h11, h13, h14, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h13, h2, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                        · linarith only [h1, h12, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                            · rcases h5bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h1, h4, hc15, hlam, hphi, ht0b, ht5b, p22_1, u0elo1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h1, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p22_1, u0elo1, u2ehi4]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h1, h4, hc35, hlam, hphi, ht0b, ht5b, p22_1, u0elo1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h1, h4, hc45, hlam, hphi, ht0b, ht5b, p22_1, u0elo1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p22_1, u2ehi4]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, h21, hc45, hlam, hphi, ht0b, ht5b, p22_1, u0elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p22_1, u0elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h3, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h7, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h11, h19, h21, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h11, h19, h6, h8, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h4, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h9, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h19, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h1, h4, hc45, hlam, hphi, ht0b, ht5b, p22_1, u0elo1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h5, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h10, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h20, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h21, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                            · linarith only [h11, h19, h21, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                          · linarith only [h2, h20, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                        · linarith only [h1, h19, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                          · linarith only [h1, h10, h51, h53, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h2, h5, h53, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                        · linarith only [h1, h4, h52, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h10, h2, h5, h51, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h1, h4, h6, h9, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                      · linarith only [h6, h61, h8, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                            · rcases h5bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h1, h4, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u0elo1, u2ehi4]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h1, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u0elo1, u2ehi4]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h1, h4, hc35, hlam, hphi, ht0b, ht5b, p66_1, u0elo1]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h1, h4, hc45, hlam, hphi, ht0b, ht5b, p66_1, u0elo1]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h0, hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi4]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h59, h65, h8, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p66_1]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p66_1, u0elo0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h3, hlam, p66_1]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h7, hlam, p66_1]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h2, h61, h63, h65, hc45, hlam, hphi, ht0b, ht5b, p66_1, u0elo1]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h2, h61, h63, hc45, hlam, hphi, ht0b, ht5b, p66_1, u0elo1]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h4, hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h59, hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h63, hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h1, h4, hc45, hlam, hphi, ht0b, ht5b, p66_1, u0elo1]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h5, hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h60, hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h64, hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [h65, hlam, p66_0]
                              · have p66_0 := h66c.1
                                have p66_1 := h66c.2.1
                                have p66_2 := h66c.2.2.1
                                have p66_3 := h66c.2.2.2
                                linarith only [hlam, p66_0]
                            · linarith only [h2, h5, h65, h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h59, h60, h61, h63, h64, h8, hc34, hlam, hphi, ht23, u2ehi4]
                        · linarith only [h1, h4, h63, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h2, h5, h59, h60, h8, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h1, h4, h59, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h3, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h1, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
            · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
              · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                    · linarith only [h0, h103, h5, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h107 | h107
                          · linarith only [h107, h2, h5, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h109 | h109
                            · linarith only [h1, h105, h109, h2, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                            · rcases h5bigk with h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [hlam, p111_0]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h100, h107, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p111_1, u0elo4, u2ehi3]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h0, h107, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p111_1, u0elo0, u2ehi3]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h1, h109, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p111_1, u0elo1]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h5, hlam, p111_1]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h0, hlam, p111_0]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [hlam, p111_0]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h107, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p111_1, u2ehi3]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h0, h109, hc34, hlam, hphi, ht0b, ht45, ht5b, p111_1, u0elo0]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h103, hlam, p111_1]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h3, hlam, p111_1]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h100, hlam, p111_1]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [hlam, p111_0]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h109, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p111_1, u0elo1]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h107, hlam, p111_1]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h4, hlam, p111_0]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h102, hlam, p111_0]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h106, hlam, p111_0]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [hlam, p111_0]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h109, hlam, p111_1]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h3, hc45, hlam, hphi, ht23, ht34, p111_1, u2ehi4]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h100, hc45, hlam, hphi, ht23, ht34, p111_1, u2ehi4]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [hc45, hlam, hphi, ht23, ht34, p111_1, u2ehi4]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [h109, hc34, hc45, hlam, hphi, p111_1]
                              · have p111_0 := h111c.1
                                have p111_1 := h111c.2.1
                                have p111_2 := h111c.2.2.1
                                have p111_3 := h111c.2.2.2
                                linarith only [hlam, p111_0]
                        · linarith only [h1, h106, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h0, h101, h103, h105, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h1, h102, h4, h99, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h141 | h141
                    · linarith only [h101, h141, h2, h5, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h101, h140, h141, hlam]
                  · linarith only [h1, h140, h4, h99, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h100, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h1, h99, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h147 | h147
          · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
            · rcases m.htr 1 2 5 (by decide) (by decide) with h149 | h149
              · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
                  · linarith only [h0, h1, h151, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
                    · linarith only [h150, h151, h153, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                        · linarith only [h1, h156, h4, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h158 | h158
                          · linarith only [h1, h153, h155, h158, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h147, h158, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                      · linarith only [h147, h150, h151, h153, h155, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h1, h150, h162, h4, hc34, hlam, hphi, ht23, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                      · linarith only [h1, h150, h165, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h167 | h167
                        · linarith only [h1, h167, h4, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h169 | h169
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h170 | h170
                            · rcases h5bigk with h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hc15, hlam, hphi, ht0b, ht5b, p171_1, u0elo4]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h0, h167, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p171_1, u0elo0, u2ehi2]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h4, hlam, p171_1]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hc45, hlam, hphi, ht0b, ht5b, p171_1, u0elo4]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h0, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h167, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u2ehi2]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h162, hlam, p171_1]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p171_1, u0elo0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h3, hlam, p171_1]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h149, hlam, p171_1]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h167, hlam, p171_1]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h169, h2, hc45, hlam, hphi, ht0b, ht5b, p171_1, u0elo1]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h170, h3, hc34, hlam, hphi, ht23, p171_1, u2ehi4]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h149, h170, hc34, hlam, hphi, ht23, p171_1, u2ehi4]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h170, hc34, hlam, hphi, ht23, p171_1, u2ehi4]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                rcases p171_3 (m.d 0 5) (by simp) with h191 | h191
                                · linarith only [h191, h4, hlam]
                                · linarith only [h147, h191, hlam]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h147, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h164, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h169, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h170, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hlam, p171_0]
                            · linarith only [h148, h150, h170, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h150, h164, h169, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h147, h148, h150, h164, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h149, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h1, h148, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
            · rcases m.htr 1 2 5 (by decide) (by decide) with h205 | h205
              · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                · rcases m.htr 1 3 5 (by decide) (by decide) with h207 | h207
                  · linarith only [h0, h1, h207, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h209 | h209
                    · linarith only [h0, h147, h2, h206, h207, h209, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h211 | h211
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
                        · linarith only [h1, h212, h4, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h214 | h214
                          · linarith only [h1, h209, h211, h214, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h216 | h216
                            · linarith only [h147, h2, h216, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h5bigk with h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [hlam, p218_0]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h204, h207, h211, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p218_1, u0elo4, u2ehi3]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h0, hc25, hlam, hphi, ht0b, ht5b, p218_1, u0elo0]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h4, hlam, p218_1]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h147, hlam, p218_1]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h0, hlam, p218_0]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [hlam, p218_0]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p218_1, u2ehi4]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h207, hlam, p218_1]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h209, hlam, p218_1]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h3, hlam, p218_1]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h205, hlam, p218_1]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [hlam, p218_0]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h212, hlam, p218_1]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h214, hlam, p218_1]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h3, hc35, hlam, hphi, ht23, p218_1, u2ehi4]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h205, h216, hc45, hlam, hphi, ht23, ht34, p218_1, u2ehi4]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h216, hc45, hlam, hphi, ht23, ht34, p218_1, u2ehi4]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [hlam, p218_0]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h216, hlam, p218_1]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h0, h204, h207, h211, hc45, hlam, hphi, ht23, ht34, p218_1, u2ehi3]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h204, h207, h211, hc45, hlam, hphi, ht23, ht34, p218_1, u2ehi3]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h211, h212, hc45, hlam, hphi, ht23, ht34, p218_1, u2ehi3]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [h1, h211, h4, hc45, hlam, hphi, ht23, ht34, p218_1, u2ehi3]
                              · have p218_0 := h218c.1
                                have p218_1 := h218c.2.1
                                have p218_2 := h218c.2.2.1
                                have p218_3 := h218c.2.2.2
                                linarith only [hlam, p218_0]
                      · linarith only [h0, h206, h207, h211, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h245 | h245
                  · linarith only [h1, h206, h245, h4, hc34, hlam, hphi, ht23, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h247 | h247
                    · linarith only [h147, h2, h206, h247, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
                      · linarith only [h1, h206, h249, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h251 | h251
                        · linarith only [h1, h251, h4, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h253 | h253
                          · linarith only [h147, h2, h253, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h255 | h255
                            · linarith only [h147, h2, h249, h255, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h204, h206, h255, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h205, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h1, h204, h4, hc35, hlam, hphi, ht23, u2ehi1]
      · linarith only [h1, h3, hc25, hlam, hphi, u2ehi2]
    · linarith only [h1, h2, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h262 | h262
    · linarith only [h1, h262, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h264 | h264
      · linarith only [h1, h264, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h266 | h266
        · rcases m.htr 0 4 5 (by decide) (by decide) with h267 | h267
          · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
            · rcases m.htr 1 2 5 (by decide) (by decide) with h269 | h269
              · linarith only [h0, h264, h269, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · linarith only [h268, h269, hc25, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h272 | h272
              · linarith only [h268, h272, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
                · rcases m.htr 1 3 5 (by decide) (by decide) with h275 | h275
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h276 | h276
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h277 | h277
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h279 | h279
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h280 | h280
                            · rcases h5bigk with h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h266, h272, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p281_1, u0elo2, u2ehi1]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h264, hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h266, hc35, hlam, hphi, ht0b, ht5b, p281_1, u0elo2]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h266, hc45, hlam, hphi, ht0b, ht5b, p281_1, u0elo2]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h0, hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h272, hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p281_1, u0elo0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p281_1, u0elo0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h0, h272, hc25, hlam, hphi, p281_1, u2ehi1]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h272, hc25, hlam, hphi, p281_1, u2ehi1]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                rcases p281_3 (m.d 0 5) (by simp) with h295 | h295
                                · linarith only [h264, h295, hlam]
                                · linarith only [h266, h295, hlam]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                rcases p281_3 (m.d 0 5) (by simp) with h298 | h298
                                · linarith only [h264, h298, hlam]
                                · linarith only [h267, h298, hlam]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h266, hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h275, hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h278, hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h266, hc45, hlam, hphi, ht0b, ht5b, p281_1, u0elo2]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h267, hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h276, hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h279, hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [h280, hlam, p281_0]
                              · have p281_0 := h281c.1
                                have p281_1 := h281c.2.1
                                have p281_2 := h281c.2.2.1
                                have p281_3 := h281c.2.2.2
                                linarith only [hlam, p281_0]
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
                                linarith only [h272, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p311_1, u0elo4, u2ehi1]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h264, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p311_1, u0elo0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h0, h280, hc34, hlam, hphi, ht0b, ht45, ht5b, p311_1, u0elo0]
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
                                linarith only [h272, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p311_1, u0elo0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h0, h280, hc34, hlam, hphi, ht0b, ht45, ht5b, p311_1, u0elo0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h264, h277, h279, hc23, hlam, hphi, p311_1, u2ehi0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h272, h277, h279, hc23, hlam, hphi, p311_1, u2ehi1]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                rcases p311_3 (m.d 0 5) (by simp) with h325 | h325
                                · linarith only [h264, h325, hlam]
                                · linarith only [h266, h325, hlam]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h277, h279, h280, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p311_1]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h266, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h275, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h278, hlam, p311_0]
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
                                linarith only [h267, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h276, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h279, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h267, h280, hc34, hlam, hphi, ht0b, ht45, ht5b, p311_1, u0elo3]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [hlam, p311_0]
                          · linarith only [h0, h276, h279, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                        · linarith only [h1, h278, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1, h277, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h342 | h342
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h344 | h344
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
                            · linarith only [h268, h272, h274, h276, h345, hc23, hlam, hphi, u2ehi1]
                            · rcases h5bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h267, h272, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p347_1, u0elo3, u2ehi1]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h264, hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h267, hc35, hlam, hphi, ht0b, ht5b, p347_1, u0elo3]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h267, h272, h276, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p347_1, u0elo3, u2ehi1]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h0, hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h272, hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p347_1, u0elo0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h276, hlam, p347_1]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h264, h344, hc24, hlam, hphi, p347_1, u2ehi0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h272, h344, hc24, hlam, hphi, p347_1, u2ehi1]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                rcases p347_3 (m.d 0 5) (by simp) with h361 | h361
                                · linarith only [h264, h361, hlam]
                                · linarith only [h266, h361, hlam]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h272, h276, h342, h344, hc23, hlam, hphi, p347_1, u2ehi1]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h266, hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h275, hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h343, hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h345, hlam, p347_1]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h267, hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h267, h272, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p347_1, u0elo4, u2ehi1]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h344, hlam, p347_0]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [h267, h345, hc34, hlam, hphi, ht0b, ht45, ht5b, p347_1, u0elo3]
                              · have p347_0 := h347c.1
                                have p347_1 := h347c.2.1
                                have p347_2 := h347c.2.2.1
                                have p347_3 := h347c.2.2.2
                                linarith only [hlam, p347_0]
                          · linarith only [h267, h344, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                        · linarith only [h1, h343, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1, h342, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h266, h274, h275, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h379 | h379
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h380 | h380
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h381 | h381
                      · linarith only [h272, h274, h379, h381, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h1, h381, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h267, h272, h274, h379, h380, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                  · linarith only [h266, h268, h379, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
            · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
              · linarith only [h0, h264, h387, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · linarith only [h386, h387, hc25, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h390 | h390
              · linarith only [h264, h386, h390, hc23, hlam, hphi, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h392 | h392
                · rcases m.htr 1 3 5 (by decide) (by decide) with h393 | h393
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h394 | h394
                    · linarith only [h262, h267, h386, h392, h394, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h397 | h397
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h398 | h398
                          · linarith only [h262, h267, h398, hc24, hlam, hphi, u2ehi0]
                          · linarith only [h262, h398, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h266, h397, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                      · linarith only [h1, h392, h396, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h266, h392, h393, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h405 | h405
                    · linarith only [h262, h267, h392, h405, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h392, h404, h405, hlam]
                  · linarith only [h266, h386, h404, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h409 | h409
          · rcases m.htr 1 2 3 (by decide) (by decide) with h410 | h410
            · rcases m.htr 1 2 5 (by decide) (by decide) with h411 | h411
              · linarith only [h0, h264, h411, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · linarith only [h410, h411, hc25, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h414 | h414
              · linarith only [h264, h410, h414, hc23, hlam, hphi, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h416 | h416
                · rcases m.htr 1 3 5 (by decide) (by decide) with h417 | h417
                  · linarith only [h1, h266, h410, h417, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h419 | h419
                    · linarith only [h416, h417, h419, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h422 | h422
                        · linarith only [h1, h266, h422, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1, h422, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h410, h421, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h426 | h426
                  · linarith only [h1, h266, h410, h426, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h428 | h428
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h429 | h429
                      · linarith only [h410, h416, h429, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h1, h429, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h409, h410, h416, h428, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h433 | h433
            · rcases m.htr 1 2 5 (by decide) (by decide) with h434 | h434
              · linarith only [h0, h264, h434, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · linarith only [h1, h433, h434, hc25, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h437 | h437
              · linarith only [h433, h437, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h439 | h439
                · rcases m.htr 1 3 5 (by decide) (by decide) with h440 | h440
                  · linarith only [h1, h266, h433, h440, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h442 | h442
                    · linarith only [h0, h262, h409, h439, h440, h442, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h444 | h444
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h445 | h445
                        · linarith only [h1, h266, h445, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1, h445, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h0, h1, h439, h440, h444, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h449 | h449
                  · linarith only [h1, h266, h439, h449, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h451 | h451
                    · linarith only [h262, h409, h439, h451, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h453 | h453
                      · linarith only [h433, h439, h453, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h1, h453, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
