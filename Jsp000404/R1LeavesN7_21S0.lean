import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h11, h13, h8, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h15, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h0, h10, h15, h8, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h0, h20, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                      · linarith only [h10, h22, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                        · rcases h2bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, h9, hc25, hlam, hphi, ht0b, ht5b, p25_1, u0elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            rcases p25_3 (m.d 0 2) (by simp) with h28 | h28
                            · rcases p25_3 (m.d 1 2) (by simp) with h29 | h29
                              · linarith only [h0, h29, hlam]
                              · linarith only [h29, h7, hlam]
                            · linarith only [h28, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            rcases p25_3 (m.d 0 2) (by simp) with h33 | h33
                            · rcases p25_3 (m.d 1 2) (by simp) with h34 | h34
                              · linarith only [h0, h34, hlam]
                              · linarith only [h34, h8, hlam]
                            · linarith only [h33, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            rcases p25_3 (m.d 0 2) (by simp) with h38 | h38
                            · rcases p25_3 (m.d 1 2) (by simp) with h39 | h39
                              · linarith only [h0, h39, hlam]
                              · linarith only [h39, h9, hlam]
                            · linarith only [h38, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u0elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, h18, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u0elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, h18, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u0elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h2, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h7, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h18, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h20, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h3, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h8, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u0elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h22, hlam, p25_1]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h4, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h9, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u0elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, h9, hc24, hlam, hphi, ht0b, ht45, ht5b, p25_1, u0elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hlam, p25_0]
                        · linarith only [h0, h18, h24, h3, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h4, h7, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h3, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
            · linarith only [h0, h2, h66, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
              · linarith only [h0, h2, h68, h7, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h73 | h73
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h74 | h74
                        · linarith only [h0, h2, h71, h74, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h2, h66, h70, h71, h74, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h66, h70, h73, hlam]
                    · linarith only [h0, h2, h5, h66, h70, h71, h72, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h80 | h80
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                        · rcases h2bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            rcases p82_3 (m.d 0 2) (by simp) with h84 | h84
                            · rcases p82_3 (m.d 1 2) (by simp) with h85 | h85
                              · linarith only [h0, h85, hlam]
                              · rcases p82_3 (m.d 2 3) (by simp) with h87 | h87
                                · linarith only [h2, h87, hlam]
                                · linarith only [h7, h87, hlam]
                            · linarith only [h0, h84, hlam]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h68, h79, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u0elo0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h68, h71, h79, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u0elo0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h68, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u0elo0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h7, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h66, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h68, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h2, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h71, hc12, hc34, hlam, hphi, ht23, p82_1]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h71, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h3, h68, h71, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u0elo0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h3, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u0elo0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p82_1, u0elo0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h3, h68, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u0elo0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h4, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h2, h79, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u0elo0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h79, hlam, p82_1]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h80, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hlam, p82_0]
                        · linarith only [h0, h3, h66, h70, h81, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h66, h70, h80, hlam]
                    · linarith only [h0, h2, h5, h7, h79, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                      · linarith only [h0, h119, h3, h66, h70, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h119, h3, h6, h66, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h117, h118, h2, h5, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h124 | h124
                      · linarith only [h0, h124, h3, h66, h70, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h124, h3, h6, h66, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h123, h2, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h128 | h128
          · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
            · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
              · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                · linarith only [h0, h129, h131, h6, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                  · linarith only [h0, h128, h133, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h135 | h135
                    · linarith only [h0, h128, h135, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                      · linarith only [h0, h129, h137, h6, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h139 | h139
                        · linarith only [h139, h5, h6, hlam]
                        · rcases h2bigk with h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h0, h130, hc25, hlam, hphi, ht0b, ht5b, p141_1, u0elo0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            rcases p141_3 (m.d 0 2) (by simp) with h144 | h144
                            · rcases p141_3 (m.d 1 2) (by simp) with h145 | h145
                              · linarith only [h0, h145, hlam]
                              · linarith only [h128, h145, hlam]
                            · linarith only [h144, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            rcases p141_3 (m.d 0 2) (by simp) with h149 | h149
                            · rcases p141_3 (m.d 1 2) (by simp) with h150 | h150
                              · linarith only [h0, h150, hlam]
                              · linarith only [h129, h150, hlam]
                            · linarith only [h149, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            rcases p141_3 (m.d 0 2) (by simp) with h154 | h154
                            · rcases p141_3 (m.d 1 2) (by simp) with h155 | h155
                              · linarith only [h0, h155, hlam]
                              · linarith only [h130, h155, hlam]
                            · linarith only [h154, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h0, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, u0elo0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h0, h133, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, u0elo0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h0, h133, h137, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, u0elo0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h2, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h128, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h133, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h135, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h3, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h129, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h1, h129, h131, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, u0elo0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h137, hlam, p141_1]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h4, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h130, hlam, p141_0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h0, h130, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, u0elo0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [h0, h130, hc24, hlam, hphi, ht0b, ht45, ht5b, p141_1, u0elo0]
                          · have p141_0 := h141c.1
                            have p141_1 := h141c.2.1
                            have p141_2 := h141c.2.2.1
                            have p141_3 := h141c.2.2.2
                            linarith only [hlam, p141_0]
              · linarith only [h0, h128, h130, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h128, h129, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
            · linarith only [h0, h128, h181, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
              · linarith only [h0, h181, h183, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h185 | h185
                · linarith only [h181, h185, h3, h6, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h188 | h188
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h189 | h189
                      · linarith only [h189, h3, h6, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h191 | h191
                        · linarith only [h0, h187, h191, h2, h6, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases h2bigk with h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            rcases p193_3 (m.d 0 2) (by simp) with h195 | h195
                            · rcases p193_3 (m.d 1 2) (by simp) with h196 | h196
                              · linarith only [h0, h196, hlam]
                              · rcases p193_3 (m.d 2 3) (by simp) with h198 | h198
                                · linarith only [h198, h2, hlam]
                                · linarith only [h128, h198, hlam]
                            · linarith only [h0, h195, hlam]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, h188, h191, hc34, hlam, hphi, ht0b, ht45, ht5b, p193_1, u0elo0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, h181, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u0elo0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, h183, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u0elo0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h128, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h181, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h183, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h2, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u0elo0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, h181, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u0elo0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, h183, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u0elo0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h3, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h3, h6, hc12, hc45, hlam, hphi, ht23, ht34, p193_1]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h187, hlam, p193_1]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h189, hlam, p193_1]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h4, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u0elo0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h188, hlam, p193_1]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, h188, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, p193_1, u0elo0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hlam, p193_0]
                    · linarith only [h0, h128, h188, h2, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                      · linarith only [h0, h227, h3, h6, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h187, h226, h227, hlam]
                    · linarith only [h0, h128, h2, h226, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h231 | h231
        · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
          · rcases m.htr 1 2 4 (by decide) (by decide) with h233 | h233
            · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
              · rcases m.htr 1 4 5 (by decide) (by decide) with h235 | h235
                · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                  · linarith only [h0, h232, h236, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h238 | h238
                    · linarith only [h0, h233, h236, h238, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h240 | h240
                      · linarith only [h0, h233, h240, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h0, h233, h235, h236, h240, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h243 | h243
                  · linarith only [h0, h232, h243, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
                    · linarith only [h0, h231, h233, h235, h243, h245, h3, h5, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h247 | h247
                      · linarith only [h233, h235, h247, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h249 | h249
                        · rcases h2bigk with h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h0, h234, hc25, hlam, hphi, ht0b, ht5b, p250_1, u0elo0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            rcases p250_3 (m.d 0 2) (by simp) with h253 | h253
                            · rcases p250_3 (m.d 1 2) (by simp) with h254 | h254
                              · linarith only [h0, h254, hlam]
                              · linarith only [h232, h254, hlam]
                            · linarith only [h253, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            rcases p250_3 (m.d 0 2) (by simp) with h258 | h258
                            · rcases p250_3 (m.d 1 2) (by simp) with h259 | h259
                              · linarith only [h0, h259, hlam]
                              · linarith only [h233, h259, hlam]
                            · linarith only [h258, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            rcases p250_3 (m.d 0 2) (by simp) with h263 | h263
                            · rcases p250_3 (m.d 1 2) (by simp) with h264 | h264
                              · linarith only [h0, h264, hlam]
                              · linarith only [h234, h264, hlam]
                            · linarith only [h263, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h0, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p250_1, u0elo0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h0, hc24, hlam, hphi, ht0b, ht45, ht5b, p250_1, u0elo0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h0, h247, hc24, hlam, hphi, ht0b, ht45, ht5b, p250_1, u0elo0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h2, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h232, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h243, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h245, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h3, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h233, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p250_1, u0elo0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h247, hlam, p250_1]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h4, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h234, hlam, p250_0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h0, h234, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p250_1, u0elo0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [h0, h234, hc24, hlam, hphi, ht0b, ht45, ht5b, p250_1, u0elo0]
                          · have p250_0 := h250c.1
                            have p250_1 := h250c.2.1
                            have p250_2 := h250c.2.2.1
                            have p250_3 := h250c.2.2.2
                            linarith only [hlam, p250_0]
                        · linarith only [h0, h231, h243, h249, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h232, h234, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h232, h233, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h291 | h291
            · linarith only [h0, h2, h232, h291, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h293 | h293
              · linarith only [h2, h232, h293, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                · rcases m.htr 2 3 4 (by decide) (by decide) with h296 | h296
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
                    · linarith only [h0, h2, h297, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h299 | h299
                      · linarith only [h296, h297, h299, hlam]
                      · linarith only [h291, h295, h299, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h302 | h302
                    · linarith only [h2, h302, h5, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h304 | h304
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h305 | h305
                        · rcases h2bigk with h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            rcases p306_3 (m.d 0 2) (by simp) with h308 | h308
                            · rcases p306_3 (m.d 1 2) (by simp) with h309 | h309
                              · linarith only [h0, h309, hlam]
                              · rcases p306_3 (m.d 2 3) (by simp) with h311 | h311
                                · linarith only [h2, h311, hlam]
                                · linarith only [h232, h311, hlam]
                            · linarith only [h0, h308, hlam]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h0, h232, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p306_1, u0elo0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h0, h291, h295, hc45, hlam, hphi, ht0b, ht5b, p306_1, u0elo0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h0, h293, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p306_1, u0elo0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h0, hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h232, hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h291, hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h293, hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h2, hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h2, h305, h5, hc12, hc34, hlam, hphi, ht23, p306_1]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h296, hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h302, hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h3, hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p306_1, u0elo0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p306_1, u0elo0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h0, h232, h3, h302, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p306_1, u0elo0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h4, hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p306_1, u0elo0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h0, h232, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p306_1, u0elo0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [h304, hlam, p306_0]
                          · have p306_0 := h306c.1
                            have p306_1 := h306c.2.1
                            have p306_2 := h306c.2.2.1
                            have p306_3 := h306c.2.2.2
                            linarith only [hlam, p306_0]
                        · linarith only [h0, h291, h295, h3, h305, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h291, h295, h304, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h340 | h340
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h341 | h341
                    · linarith only [h0, h2, h341, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h343 | h343
                      · linarith only [h0, h295, h3, h343, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h231, h291, h3, h343, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h346 | h346
                    · linarith only [h2, h346, h5, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h348 | h348
                      · linarith only [h0, h291, h295, h3, h348, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h231, h291, h3, h348, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h351 | h351
          · rcases m.htr 1 2 4 (by decide) (by decide) with h352 | h352
            · rcases m.htr 1 2 5 (by decide) (by decide) with h353 | h353
              · rcases m.htr 1 4 5 (by decide) (by decide) with h354 | h354
                · linarith only [h0, h231, h352, h354, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h356 | h356
                  · linarith only [h0, h351, h356, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h358 | h358
                    · linarith only [h0, h352, h356, h358, h5, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h360 | h360
                      · linarith only [h0, h352, h354, h360, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h362 | h362
                        · rcases h2bigk with h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h353, h356, h360, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p363_1, u0elo0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            rcases p363_3 (m.d 0 2) (by simp) with h366 | h366
                            · rcases p363_3 (m.d 1 2) (by simp) with h367 | h367
                              · linarith only [h0, h367, hlam]
                              · linarith only [h351, h367, hlam]
                            · linarith only [h366, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            rcases p363_3 (m.d 0 2) (by simp) with h371 | h371
                            · rcases p363_3 (m.d 1 2) (by simp) with h372 | h372
                              · linarith only [h0, h372, hlam]
                              · linarith only [h352, h372, hlam]
                            · linarith only [h371, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            rcases p363_3 (m.d 0 2) (by simp) with h376 | h376
                            · rcases p363_3 (m.d 1 2) (by simp) with h377 | h377
                              · linarith only [h0, h377, hlam]
                              · linarith only [h353, h377, hlam]
                            · linarith only [h376, hlam, p363_0]
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
                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p363_1, u0elo0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h356, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p363_1, u0elo0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h356, h360, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p363_1, u0elo0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h2, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h351, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h356, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h358, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h3, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h352, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p363_1, u0elo0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h360, hlam, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h4, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h353, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h353, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p363_1, u0elo0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h353, hc24, hlam, hphi, ht0b, ht45, ht5b, p363_1, u0elo0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                        · rcases h2bigk with h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h0, h353, hc25, hlam, hphi, ht0b, ht5b, p401_1, u0elo0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            rcases p401_3 (m.d 0 2) (by simp) with h404 | h404
                            · rcases p401_3 (m.d 1 2) (by simp) with h405 | h405
                              · linarith only [h0, h405, hlam]
                              · linarith only [h351, h405, hlam]
                            · linarith only [h404, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            rcases p401_3 (m.d 0 2) (by simp) with h409 | h409
                            · rcases p401_3 (m.d 1 2) (by simp) with h410 | h410
                              · linarith only [h0, h410, hlam]
                              · linarith only [h352, h410, hlam]
                            · linarith only [h409, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            rcases p401_3 (m.d 0 2) (by simp) with h414 | h414
                            · rcases p401_3 (m.d 1 2) (by simp) with h415 | h415
                              · linarith only [h0, h415, hlam]
                              · linarith only [h353, h415, hlam]
                            · linarith only [h414, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h0, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p401_1, u0elo0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h0, h356, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p401_1, u0elo0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h0, h356, h360, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p401_1, u0elo0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h2, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h351, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h356, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h358, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h3, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h352, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p401_1, u0elo0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h360, hlam, p401_1]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h4, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h353, hlam, p401_0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h0, h353, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p401_1, u0elo0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [h0, h353, hc24, hlam, hphi, ht0b, ht45, ht5b, p401_1, u0elo0]
                          · have p401_0 := h401c.1
                            have p401_1 := h401c.2.1
                            have p401_2 := h401c.2.2.1
                            have p401_3 := h401c.2.2.2
                            linarith only [hlam, p401_0]
              · linarith only [h0, h351, h353, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h3, h351, h352, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h441 | h441
            · linarith only [h0, h2, h351, h441, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h443 | h443
              · linarith only [h0, h2, h351, h443, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
                · linarith only [h231, h3, h441, h445, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
                    · linarith only [h0, h2, h448, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h450 | h450
                      · linarith only [h0, h231, h4, h447, h448, h450, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h452 | h452
                        · linarith only [h0, h231, h4, h447, h448, h452, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases h2bigk with h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            rcases p454_3 (m.d 0 2) (by simp) with h456 | h456
                            · rcases p454_3 (m.d 1 2) (by simp) with h457 | h457
                              · linarith only [h0, h457, hlam]
                              · rcases p454_3 (m.d 2 3) (by simp) with h459 | h459
                                · linarith only [h2, h459, hlam]
                                · linarith only [h351, h459, hlam]
                            · linarith only [h0, h456, hlam]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, h447, hc34, hlam, hphi, ht0b, ht45, ht5b, p454_1, u0elo0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, h441, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1, u0elo0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, h443, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1, u0elo0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h351, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h441, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h443, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h2, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h2, h5, hc12, hc35, hlam, hphi, ht23, p454_1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, h2, h441, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1, u0elo0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h448, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h3, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1, u0elo0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h447, hlam, p454_1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h450, hlam, p454_1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h4, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1, u0elo0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p454_1, u0elo0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, h4, h441, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1, u0elo0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [hlam, p454_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h486 | h486
                    · linarith only [h447, h486, h5, hc03, hc34, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h488 | h488
                      · linarith only [h231, h3, h488, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h490 | h490
                        · linarith only [h231, h3, h351, h447, h490, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h351, h447, h490, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h493 | h493
      · linarith only [h2, h4, h493, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h495 | h495
        · linarith only [h3, h4, h495, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
          · rcases m.htr 1 2 4 (by decide) (by decide) with h498 | h498
            · rcases m.htr 1 2 5 (by decide) (by decide) with h499 | h499
              · linarith only [h0, h4, h499, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h501 | h501
                · linarith only [h0, h4, h495, h498, h501, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h503 | h503
                  · linarith only [h0, h497, h503, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h505 | h505
                    · linarith only [h493, h503, h505, hc03, hc34, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h507 | h507
                      · linarith only [h0, h4, h495, h498, h507, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h509 | h509
                        · linarith only [h0, h4, h498, h503, h507, h509, hc23, hc34, hlam, hphi]
                        · rcases h2bigk with h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h498, h503, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p511_1, u0elo1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h4, h505, h509, hc23, hc45, hlam, hphi, ht34, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h4, h503, h505, h509, hc23, hc45, hlam, hphi, ht34, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h4, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h0, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p511_1, u0elo0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h0, h4, h503, h505, h509, hc23, hc45, hlam, hphi, ht34, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h499, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h2, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h497, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h503, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h505, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h3, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h498, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h3, h4, h505, h509, hc23, hc45, hlam, hphi, ht34, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h507, hlam, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h2, h505, h509, hc23, hc45, hlam, hphi, ht34, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h498, h505, h509, hc24, hc45, hlam, hphi, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            rcases p511_3 (m.d 0 2) (by simp) with h534 | h534
                            · linarith only [h4, h534, hlam]
                            · linarith only [h2, h534, hlam]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            rcases p511_3 (m.d 0 2) (by simp) with h537 | h537
                            · linarith only [h4, h537, hlam]
                            · linarith only [h3, h537, hlam]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [hlam, p511_0]
            · linarith only [h3, h4, h498, hc12, hc25, hlam, hphi]
          · linarith only [h2, h4, h497, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h543 | h543
    · rcases m.htr 0 3 5 (by decide) (by decide) with h544 | h544
      · rcases m.htr 0 4 5 (by decide) (by decide) with h545 | h545
        · rcases m.htr 1 2 3 (by decide) (by decide) with h546 | h546
          · rcases m.htr 1 2 4 (by decide) (by decide) with h547 | h547
            · linarith only [h0, h3, h547, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h549 | h549
              · rcases m.htr 1 4 5 (by decide) (by decide) with h550 | h550
                · rcases m.htr 2 3 4 (by decide) (by decide) with h551 | h551
                  · linarith only [h0, h546, h551, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h553 | h553
                    · linarith only [h0, h546, h553, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h2, h3, h544, h551, h553, hc23, hc34, hlam, hphi]
                · linarith only [h545, h547, h549, h550, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
              · linarith only [h543, h546, h549, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h2, h3, h546, hc12, hc24, hlam, hphi]
        · linarith only [h2, h3, h544, h545, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h560 | h560
        · rcases m.htr 1 2 3 (by decide) (by decide) with h561 | h561
          · rcases m.htr 1 2 4 (by decide) (by decide) with h562 | h562
            · linarith only [h0, h3, h562, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h564 | h564
              · rcases m.htr 1 4 5 (by decide) (by decide) with h565 | h565
                · rcases m.htr 2 3 4 (by decide) (by decide) with h566 | h566
                  · linarith only [h0, h561, h566, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h568 | h568
                    · linarith only [h0, h544, h561, h568, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h570 | h570
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h571 | h571
                        · rcases h2bigk with h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h564, h568, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1, u0elo1]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h3, h566, hc23, hc34, hlam, hphi, p572_1]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h3, hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h3, h566, h568, hc23, hc34, hlam, hphi, p572_1]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h0, hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1, u0elo0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h562, hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h0, h568, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1, u0elo0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h2, hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h561, hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h566, hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h568, hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h2, h566, hc23, hc34, hlam, hphi, p572_1]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h561, h566, hc23, hc34, hlam, hphi, p572_1]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            rcases p572_3 (m.d 0 2) (by simp) with h590 | h590
                            · linarith only [h3, h590, hlam]
                            · linarith only [h2, h590, hlam]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            rcases p572_3 (m.d 0 2) (by simp) with h594 | h594
                            · linarith only [h3, h594, hlam]
                            · linarith only [h543, h594, hlam]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h543, hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h564, hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h0, h564, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1, u0elo1]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [h570, hlam, p572_0]
                          · have p572_0 := h572c.1
                            have p572_1 := h572c.2.1
                            have p572_2 := h572c.2.2.1
                            have p572_3 := h572c.2.2.2
                            linarith only [hlam, p572_0]
                        · linarith only [h0, h3, h564, h566, h570, h571, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h3, h564, h568, h570, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h560, h562, h564, h565, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
              · linarith only [h543, h561, h564, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h2, h3, h561, hc12, hc24, hlam, hphi]
        · linarith only [h3, h543, h560, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h608 | h608
      · linarith only [h2, h543, h608, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h610 | h610
        · rcases m.htr 1 2 3 (by decide) (by decide) with h611 | h611
          · rcases m.htr 1 2 4 (by decide) (by decide) with h612 | h612
            · linarith only [h0, h3, h612, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h614 | h614
              · linarith only [h0, h543, h614, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h616 | h616
                · rcases m.htr 2 3 4 (by decide) (by decide) with h617 | h617
                  · linarith only [h0, h611, h617, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h619 | h619
                    · linarith only [h1, h608, h611, h614, h619, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h621 | h621
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h622 | h622
                        · rcases h2bigk with h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h543, h617, h621, hc12, hc34, hlam, hphi, ht23, p623_1]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h543, h617, h621, hc23, hc34, hlam, hphi, p623_1]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h3, hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h543, hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h0, hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p623_1, u0elo0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h612, hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h614, hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h2, hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h611, hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h617, hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h619, hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h2, h617, hc23, hc34, hlam, hphi, p623_1]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h611, h617, hc23, hc34, hlam, hphi, p623_1]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            rcases p623_3 (m.d 0 2) (by simp) with h641 | h641
                            · linarith only [h3, h641, hlam]
                            · linarith only [h2, h641, hlam]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h0, h543, h611, h617, hc23, hc34, hlam, hphi, p623_1]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h0, h611, h619, hc23, hc35, hlam, hphi, p623_1]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h611, h619, hc23, hc35, hlam, hphi, p623_1]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            rcases p623_3 (m.d 0 2) (by simp) with h648 | h648
                            · linarith only [h543, h648, hlam]
                            · linarith only [h2, h648, hlam]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [h621, hlam, p623_0]
                          · have p623_0 := h623c.1
                            have p623_1 := h623c.2.1
                            have p623_2 := h623c.2.2.1
                            have p623_3 := h623c.2.2.2
                            linarith only [hlam, p623_0]
                        · linarith only [h0, h3, h611, h617, h622, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1, h3, h611, h616, h621, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h610, h611, h612, h616, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
          · linarith only [h2, h543, h611, hc12, hc25, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h657 | h657
          · rcases m.htr 1 2 4 (by decide) (by decide) with h658 | h658
            · linarith only [h0, h3, h658, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
              · linarith only [h0, h543, h660, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h662 | h662
                · linarith only [h0, h1, h3, h610, h657, h662, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h664 | h664
                  · linarith only [h0, h657, h664, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h666 | h666
                    · linarith only [h1, h657, h658, h662, h666, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h668 | h668
                      · linarith only [h0, h3, h610, h657, h664, h668, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h3, h657, h668, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h2, h3, h657, hc12, hc24, hlam, hphi]

end R2N4
