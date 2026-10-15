import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4448000 in
set_option maxHeartbeats 4448000 in
theorem r1l7_20_12_13_M_LR_L_I_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
            · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
              · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                      · linarith only [h0, h12, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h12, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h10, h11, h2, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h0, h10, h16, h2, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h10, h18, h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h16, h20, h7, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                          · linarith only [h0, h22, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                            · linarith only [h0, h2, h22, h24, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases h2bigk with h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h0, h9, hc25, hlam, hphi, ht0b, ht5b, p26_1, u0elo0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                rcases p26_3 (m.d 0 2) (by simp) with h29 | h29
                                · rcases p26_3 (m.d 1 2) (by simp) with h30 | h30
                                  · linarith only [h0, h30, hlam]
                                  · linarith only [h30, h7, hlam]
                                · linarith only [h29, hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                rcases p26_3 (m.d 0 2) (by simp) with h34 | h34
                                · rcases p26_3 (m.d 1 2) (by simp) with h35 | h35
                                  · linarith only [h0, h35, hlam]
                                  · linarith only [h35, h8, hlam]
                                · linarith only [h34, hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                rcases p26_3 (m.d 0 2) (by simp) with h39 | h39
                                · rcases p26_3 (m.d 1 2) (by simp) with h40 | h40
                                  · linarith only [h0, h40, hlam]
                                  · linarith only [h40, h9, hlam]
                                · linarith only [h39, hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h0, hlam, p26_1]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u0elo0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h0, h18, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u0elo0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h0, h18, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u0elo0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h2, hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h7, hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h18, hlam, p26_1]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h20, hlam, p26_1]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h3, hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h8, hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u0elo0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h22, hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h4, hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h9, hlam, p26_0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h0, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u0elo0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [h0, h9, hc24, hlam, hphi, ht0b, ht45, ht5b, p26_1, u0elo0]
                              · have p26_0 := h26c.1
                                have p26_1 := h26c.2.1
                                have p26_2 := h26c.2.2.1
                                have p26_3 := h26c.2.2.2
                                linarith only [hlam, p26_0]
                · linarith only [h0, h4, h7, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h3, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
              · linarith only [h0, h2, h66, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
                · linarith only [h0, h2, h68, h7, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h70 | h70
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                            · linarith only [h1, h70, h75, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h0, h2, h72, h74, h75, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                            · linarith only [h0, h2, h5, h74, h78, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases h2bigk with h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                rcases p80_3 (m.d 0 2) (by simp) with h82 | h82
                                · rcases p80_3 (m.d 1 2) (by simp) with h83 | h83
                                  · linarith only [h0, h83, hlam]
                                  · rcases p80_3 (m.d 2 3) (by simp) with h85 | h85
                                    · linarith only [h2, h85, hlam]
                                    · linarith only [h7, h85, hlam]
                                · linarith only [h0, h82, hlam]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h66, h73, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u0elo0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h66, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u0elo0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h66, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u0elo0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, hlam, p80_1]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h7, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h66, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h68, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h2, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u0elo0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h2, h66, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u0elo0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h2, h66, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u0elo0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h3, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h74, hc12, hc45, hlam, hphi, ht23, ht34, p80_1]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h72, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h74, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h4, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u0elo0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h73, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, p80_1, u0elo0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hlam, p80_0]
                        · linarith only [h1, h71, h73, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h2, h5, h7, h71, h72, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h0, h2, h6, h70, h71, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                    · linarith only [h0, h115, h2, h5, h70, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                      · linarith only [h0, h117, h2, h70, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h117, h2, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h120 | h120
            · rcases m.htr 1 2 4 (by decide) (by decide) with h121 | h121
              · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
                    · linarith only [h124, h6, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                      · linarith only [h0, h120, h126, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h123, h126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h123, h5, h6, hc13, hc35, hlam, hphi]
                · linarith only [h121, h122, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h0, h120, h121, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
              · linarith only [h0, h120, h132, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                · linarith only [h0, h120, h134, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
                    · linarith only [h137, h5, h6, hc13, hlam, hphi, ht01, u0ehi8]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h139 | h139
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                        · linarith only [h0, h140, h2, h5, h6, hlam, hphi, u0ehi8, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                          · linarith only [h139, h140, h142, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
                            · linarith only [h132, h142, h144, hc12, hc34, hlam, hphi, ht23]
                            · rcases h2bigk with h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                rcases p146_3 (m.d 0 2) (by simp) with h148 | h148
                                · rcases p146_3 (m.d 1 2) (by simp) with h149 | h149
                                  · linarith only [h0, h149, hlam]
                                  · rcases p146_3 (m.d 2 3) (by simp) with h151 | h151
                                    · linarith only [h151, h2, hlam]
                                    · linarith only [h120, h151, hlam]
                                · linarith only [h0, h148, hlam]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h0, h132, h139, h144, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p146_1, u0ehi8, u0elo0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h0, h132, h144, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p146_1, u0ehi8, u0elo0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h0, h134, h136, h137, h144, h5, h6, hc34, hc45, hlam, hphi, p146_1, u0ehi8, u0elo0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h0, hlam, p146_1]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h120, hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h132, hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h134, hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h2, hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h0, h144, h2, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p146_1, u0ehi8, u0elo0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h0, h132, h144, h2, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p146_1, u0ehi8, u0elo0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h140, hlam, p146_1]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h3, hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h0, h144, h3, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p146_1, u0ehi8, u0elo0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h139, hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h142, hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h4, hlam, p146_0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h0, h144, h4, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p146_1, u0ehi8, u0elo0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h0, h144, h4, h5, h6, hc23, hc45, hlam, hphi, ht34, p146_1, u0ehi8, u0elo0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [h0, h132, h144, h4, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p146_1, u0ehi8, u0elo0]
                              · have p146_0 := h146c.1
                                have p146_1 := h146c.2.1
                                have p146_2 := h146c.2.2.1
                                have p146_3 := h146c.2.2.2
                                linarith only [hlam, p146_0]
                      · linarith only [h1, h136, h139, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h120, h136, h5, h6, hc12, hc35, hlam, hphi, ht23]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h180 | h180
          · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
            · rcases m.htr 1 2 4 (by decide) (by decide) with h182 | h182
              · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
                  · linarith only [h184, h5, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                      · linarith only [h0, h180, h181, h187, h5, hlam, hphi, u0ehi9, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h189 | h189
                        · linarith only [h0, h182, h187, h189, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h180, h189, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h180, h186, h5, hc13, hc34, hlam, hphi]
                · linarith only [h0, h182, h183, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h0, h181, h182, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h195 | h195
              · linarith only [h0, h181, h195, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                · linarith only [h0, h181, h197, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h199 | h199
                  · linarith only [h199, h5, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                      · linarith only [h0, h180, h2, h202, h5, hlam, hphi, u0ehi9, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h205 | h205
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                            · rcases h2bigk with h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                rcases p207_3 (m.d 0 2) (by simp) with h209 | h209
                                · rcases p207_3 (m.d 1 2) (by simp) with h210 | h210
                                  · linarith only [h0, h210, hlam]
                                  · rcases p207_3 (m.d 2 3) (by simp) with h212 | h212
                                    · linarith only [h2, h212, hlam]
                                    · linarith only [h181, h212, hlam]
                                · linarith only [h0, h209, hlam]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h197, h204, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u0elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h195, h199, h201, hc35, hlam, hphi, ht0b, ht5b, p207_1, u0elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h197, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u0elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, hlam, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h181, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h195, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h197, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h2, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u0elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h202, hlam, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h197, h202, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u0elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h3, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u0elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p207_1, u0elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h197, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u0elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h4, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h2, h204, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u0elo0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h204, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h205, hlam, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                            · linarith only [h180, h206, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                          · linarith only [h202, h204, h205, hlam]
                        · linarith only [h1, h201, h204, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h180, h201, h5, hc13, hc34, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
            · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
              · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                  · linarith only [h246, h5, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h248 | h248
                    · linarith only [h180, h244, h246, h248, hc12, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h250 | h250
                      · linarith only [h250, h5, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h252 | h252
                        · linarith only [h0, h180, h244, h250, h252, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h254 | h254
                          · linarith only [h0, h244, h254, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h256 | h256
                            · rcases h2bigk with h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h0, h245, h250, h254, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1, u0elo0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                rcases p257_3 (m.d 0 2) (by simp) with h260 | h260
                                · rcases p257_3 (m.d 1 2) (by simp) with h261 | h261
                                  · linarith only [h0, h261, hlam]
                                  · linarith only [h243, h261, hlam]
                                · linarith only [h260, hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                rcases p257_3 (m.d 0 2) (by simp) with h265 | h265
                                · rcases p257_3 (m.d 1 2) (by simp) with h266 | h266
                                  · linarith only [h0, h266, hlam]
                                  · linarith only [h244, h266, hlam]
                                · linarith only [h265, hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                rcases p257_3 (m.d 0 2) (by simp) with h270 | h270
                                · rcases p257_3 (m.d 1 2) (by simp) with h271 | h271
                                  · linarith only [h0, h271, hlam]
                                  · linarith only [h245, h271, hlam]
                                · linarith only [h270, hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h0, hlam, p257_1]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1, u0elo0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h0, h250, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1, u0elo0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h0, h250, h254, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1, u0elo0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h2, hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h243, hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h250, hlam, p257_1]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h252, hlam, p257_1]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h3, hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h244, hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h254, hc23, hc45, hlam, hphi, ht34, p257_1]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h254, hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h4, hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h245, hlam, p257_0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h0, h245, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1, u0elo0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [h0, h245, hc24, hlam, hphi, ht0b, ht45, ht5b, p257_1, u0elo0]
                              · have p257_0 := h257c.1
                                have p257_1 := h257c.2.1
                                have p257_2 := h257c.2.2.1
                                have p257_3 := h257c.2.2.2
                                linarith only [hlam, p257_0]
                            · linarith only [h256, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                · linarith only [h0, h243, h245, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h243, h244, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
              · linarith only [h0, h2, h243, h298, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h300 | h300
                · linarith only [h0, h2, h243, h300, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h302 | h302
                  · linarith only [h302, h5, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h304 | h304
                    · linarith only [h0, h180, h298, h3, h302, h304, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                      · linarith only [h0, h2, h306, h5, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h308 | h308
                        · linarith only [h0, h180, h3, h306, h308, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h310 | h310
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h311 | h311
                            · rcases h2bigk with h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                rcases p312_3 (m.d 0 2) (by simp) with h314 | h314
                                · rcases p312_3 (m.d 1 2) (by simp) with h315 | h315
                                  · linarith only [h0, h315, hlam]
                                  · rcases p312_3 (m.d 2 3) (by simp) with h317 | h317
                                    · linarith only [h2, h317, hlam]
                                    · linarith only [h243, h317, hlam]
                                · linarith only [h0, h314, hlam]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h243, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p312_1, u0elo0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h310, hc45, hlam, hphi, ht0b, ht5b, p312_1, u0elo0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h300, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p312_1, u0elo0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, hlam, p312_1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h243, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h298, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h300, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h2, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p312_1, u0elo0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h306, hlam, p312_1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h308, hlam, p312_1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h3, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p312_1, u0elo0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p312_1, u0elo0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h243, h3, h308, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p312_1, u0elo0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h4, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p312_1, u0elo0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h243, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p312_1, u0elo0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h310, hlam, p312_1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                            · linarith only [h311, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
                            · linarith only [h243, h306, h310, h345, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h243, h306, h310, h345, h4, h5, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h348 | h348
        · rcases m.htr 0 3 5 (by decide) (by decide) with h349 | h349
          · linarith only [h2, h349, h4, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h351 | h351
            · rcases m.htr 1 2 4 (by decide) (by decide) with h352 | h352
              · rcases m.htr 1 2 5 (by decide) (by decide) with h353 | h353
                · linarith only [h0, h353, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h356 | h356
                    · linarith only [h0, h348, h349, h351, h356, hlam, hphi, u0ehi8, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h358 | h358
                      · linarith only [h0, h351, h358, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h348, h349, h358, hc23, hc35, hlam, hphi]
                  · linarith only [h348, h349, h355, hc13, hc35, hlam, hphi]
              · linarith only [h3, h352, h4, hc12, hc25, hlam, hphi]
            · linarith only [h2, h351, h4, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h364 | h364
          · linarith only [h3, h348, h364, h4, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h366 | h366
            · rcases m.htr 1 2 4 (by decide) (by decide) with h367 | h367
              · rcases m.htr 1 2 5 (by decide) (by decide) with h368 | h368
                · linarith only [h368, h4, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h370 | h370
                  · linarith only [h348, h370, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h372 | h372
                    · linarith only [h0, h364, h367, h370, h372, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h374 | h374
                      · linarith only [h348, h374, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h376 | h376
                        · linarith only [h0, h364, h367, h374, h376, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                          · linarith only [h0, h367, h378, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h380 | h380
                            · linarith only [h3, h348, h378, h380, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                            · linarith only [h348, h380, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h3, h367, h4, hc12, hc25, hlam, hphi]
            · linarith only [h2, h366, h4, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h385 | h385
      · rcases m.htr 0 3 4 (by decide) (by decide) with h386 | h386
        · linarith only [h2, h3, h386, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h388 | h388
          · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
            · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
              · linarith only [h2, h3, h388, h390, hc12, hlam, hphi, ht01, u0ehi9]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h392 | h392
                · rcases m.htr 1 3 4 (by decide) (by decide) with h393 | h393
                  · linarith only [h386, h388, h393, hc13, hlam, hphi, ht01, u0ehi9]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h395 | h395
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
                      · linarith only [h386, h388, h396, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h398 | h398
                        · linarith only [h0, h389, h398, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h2, h3, h388, h396, h398, hc23, hc34, hlam, hphi]
                    · linarith only [h386, h388, h395, hc13, hc34, hlam, hphi]
                · linarith only [h3, h385, h392, hc12, hc24, hlam, hphi]
            · linarith only [h2, h3, h389, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
            · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
              · linarith only [h3, h405, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h407 | h407
                · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
                  · linarith only [h386, h408, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h410 | h410
                    · linarith only [h0, h388, h404, h410, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                      · linarith only [h386, h412, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h414 | h414
                        · linarith only [h0, h388, h404, h414, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h416 | h416
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h417 | h417
                            · rcases h2bigk with h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h407, h414, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p418_1, u0elo1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h3, h412, hc23, hc34, hlam, hphi, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h3, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h3, h412, h414, hc23, hc34, hlam, hphi, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, h3, h385, h388, h412, hc23, hc34, hlam, hphi, p418_1, u0ehi7, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h405, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, h3, h385, h388, h412, h414, hc23, hc34, hlam, hphi, p418_1, u0ehi7, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h2, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h404, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h412, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h414, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h385, h388, h412, hc34, hlam, hphi, ht01, ht12, ht23, p418_1, u0ehi7]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h404, h412, hc23, hc34, hlam, hphi, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                rcases p418_3 (m.d 0 2) (by simp) with h436 | h436
                                · linarith only [h3, h436, hlam]
                                · linarith only [h2, h436, hlam]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                rcases p418_3 (m.d 0 2) (by simp) with h440 | h440
                                · linarith only [h3, h440, hlam]
                                · linarith only [h385, h440, hlam]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h385, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h407, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, h407, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p418_1, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h416, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                            · linarith only [h0, h3, h385, h388, h407, h412, h416, h417, hlam, hphi, u0ehi7, u0elo0]
                          · linarith only [h3, h385, h388, h416, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                · linarith only [h3, h385, h407, hc12, hc24, hlam, hphi]
            · linarith only [h2, h3, h404, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h452 | h452
        · linarith only [h2, h3, h452, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h454 | h454
          · linarith only [h2, h385, h454, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h456 | h456
            · rcases m.htr 1 2 4 (by decide) (by decide) with h457 | h457
              · linarith only [h3, h457, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
                · linarith only [h0, h2, h385, h459, hlam, hphi, u0ehi7, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h461 | h461
                  · linarith only [h452, h461, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h463 | h463
                    · linarith only [h0, h454, h456, h463, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h465 | h465
                      · linarith only [h452, h465, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h467 | h467
                        · linarith only [h0, h454, h456, h467, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h469 | h469
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h470 | h470
                            · rcases h2bigk with h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h385, h465, h469, hc12, hc34, hlam, hphi, ht23, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h385, h465, h469, hc23, hc34, hlam, hphi, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h3, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h385, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h0, hlam, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h0, h2, h385, h465, h469, hc23, hc34, hlam, hphi, p471_1, u0ehi7, u0elo0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h457, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h459, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h2, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h456, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h465, hlam, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h467, hlam, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h2, h465, hc34, hlam, hphi, ht01, ht12, ht23, p471_1, u0ehi7]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h456, h465, hc23, hc34, hlam, hphi, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                rcases p471_3 (m.d 0 2) (by simp) with h489 | h489
                                · linarith only [h3, h489, hlam]
                                · linarith only [h2, h489, hlam]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h2, h385, h465, hc34, hlam, hphi, ht01, ht12, ht23, p471_1, u0ehi7]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h2, hc25, hlam, hphi, ht01, ht12, p471_1, u0ehi7]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h456, h467, hc23, hc35, hlam, hphi, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                rcases p471_3 (m.d 0 2) (by simp) with h496 | h496
                                · linarith only [h385, h496, hlam]
                                · linarith only [h2, h496, hlam]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h469, hlam, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [hlam, p471_0]
                            · linarith only [h465, h469, h470, hlam]
                          · linarith only [h2, h3, h469, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
            · linarith only [h2, h3, h456, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h504 | h504
    · rcases m.htr 0 2 5 (by decide) (by decide) with h505 | h505
      · rcases m.htr 0 3 4 (by decide) (by decide) with h506 | h506
        · rcases m.htr 0 3 5 (by decide) (by decide) with h507 | h507
          · rcases m.htr 1 2 3 (by decide) (by decide) with h508 | h508
            · linarith only [h2, h508, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h510 | h510
              · rcases m.htr 1 2 5 (by decide) (by decide) with h511 | h511
                · rcases m.htr 1 3 4 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h513 | h513
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h515 | h515
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h516 | h516
                          · linarith only [h1, h508, h510, h516, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h518 | h518
                            · linarith only [h514, h516, h518, hlam]
                            · rcases h2bigk with h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h2, hc12, hc23, hlam, hphi, p520_1]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h2, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                rcases p520_3 (m.d 0 2) (by simp) with h524 | h524
                                · rcases p520_3 (m.d 1 2) (by simp) with h525 | h525
                                  · linarith only [h0, h525, hlam]
                                  · linarith only [h510, h525, hlam]
                                · linarith only [h524, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                rcases p520_3 (m.d 0 2) (by simp) with h529 | h529
                                · rcases p520_3 (m.d 1 2) (by simp) with h530 | h530
                                  · linarith only [h0, h530, hlam]
                                  · linarith only [h511, h530, hlam]
                                · linarith only [h529, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h0, hlam, p520_1]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h508, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h0, h514, hc34, hlam, hphi, ht0b, ht45, ht5b, p520_1, u0elo0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h1, h508, h514, h516, hc34, hlam, hphi, ht0b, ht45, ht5b, p520_1, u0elo0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p520_1, u0ehi6]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                rcases p520_3 (m.d 0 2) (by simp) with h540 | h540
                                · linarith only [h2, h540, hlam]
                                · linarith only [h0, h540, hlam]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                rcases p520_3 (m.d 0 2) (by simp) with h544 | h544
                                · linarith only [h2, h544, hlam]
                                · linarith only [h504, h544, hlam]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                rcases p520_3 (m.d 0 2) (by simp) with h547 | h547
                                · linarith only [h2, h547, hlam]
                                · linarith only [h505, h547, hlam]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h504, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h510, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h514, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h516, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h505, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h511, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h515, hlam, p520_0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [h1, h508, h511, hc24, hlam, hphi, ht0b, ht45, ht5b, p520_1, u0elo0]
                              · have p520_0 := h520c.1
                                have p520_1 := h520c.2.1
                                have p520_2 := h520c.2.2.1
                                have p520_3 := h520c.2.2.2
                                linarith only [hlam, p520_0]
                        · linarith only [h2, h505, h515, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                      · linarith only [h2, h505, h514, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h507, h508, h511, h513, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h1, h506, h508, h510, h512, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h505, h510, h511, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h2, h504, h510, hc12, hc23, hlam, hphi]
          · linarith only [h2, h505, h507, hlam]
        · linarith only [h2, h504, h506, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h568 | h568
        · rcases m.htr 0 3 5 (by decide) (by decide) with h569 | h569
          · rcases m.htr 1 2 3 (by decide) (by decide) with h570 | h570
            · linarith only [h0, h2, h570, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h572 | h572
              · rcases m.htr 1 2 5 (by decide) (by decide) with h573 | h573
                · linarith only [h504, h505, h573, hc12, hlam, hphi, ht01, u0ehi8]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h575 | h575
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h577 | h577
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h578 | h578
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h579 | h579
                          · linarith only [h1, h572, h573, h576, h579, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h581 | h581
                            · linarith only [h504, h505, h579, h581, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                            · rcases h2bigk with h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h505, h579, hc12, hc45, hlam, hphi, ht23, ht34, p583_1]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h2, hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h505, h579, hc24, hc45, hlam, hphi, p583_1]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h505, hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h0, hlam, p583_1]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h570, hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h0, h504, h505, h579, hc24, hc45, hlam, hphi, p583_1, u0ehi8, u0elo0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h573, hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h504, hc23, hlam, hphi, ht01, ht12, p583_1, u0ehi8]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                rcases p583_3 (m.d 0 2) (by simp) with h595 | h595
                                · linarith only [h2, h595, hlam]
                                · linarith only [h0, h595, hlam]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                rcases p583_3 (m.d 0 2) (by simp) with h599 | h599
                                · linarith only [h2, h599, hlam]
                                · linarith only [h504, h599, hlam]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h504, h505, hc23, hlam, hphi, ht01, ht12, p583_1, u0ehi8]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h504, hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h572, hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h577, hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h579, hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h504, h579, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p583_1, u0ehi8]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h572, h579, hc24, hc45, hlam, hphi, p583_1]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [h578, hlam, p583_0]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                rcases p583_3 (m.d 0 2) (by simp) with h611 | h611
                                · linarith only [h505, h611, hlam]
                                · linarith only [h504, h611, hlam]
                              · have p583_0 := h583c.1
                                have p583_1 := h583c.2.1
                                have p583_2 := h583c.2.2.1
                                have p583_3 := h583c.2.2.2
                                linarith only [hlam, p583_0]
                        · linarith only [h2, h504, h578, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                      · linarith only [h2, h504, h577, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                    · linarith only [h569, h575, h576, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h1, h568, h570, h572, h575, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h2, h504, h572, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
            · linarith only [h0, h2, h620, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h622 | h622
              · rcases m.htr 1 2 5 (by decide) (by decide) with h623 | h623
                · linarith only [h504, h505, h623, hc12, hlam, hphi, ht01, u0ehi8]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h625 | h625
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h626 | h626
                    · linarith only [h1, h569, h626, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h628 | h628
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h629 | h629
                        · linarith only [h2, h504, h569, h629, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                        · linarith only [h2, h504, h629, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                      · linarith only [h2, h504, h628, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                  · linarith only [h568, h569, h620, h625, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h2, h504, h569, h622, hc12, hc35, hlam, hphi, ht23]
        · linarith only [h2, h504, h568, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h636 | h636
      · rcases m.htr 0 3 4 (by decide) (by decide) with h637 | h637
        · rcases m.htr 0 3 5 (by decide) (by decide) with h638 | h638
          · rcases m.htr 1 2 3 (by decide) (by decide) with h639 | h639
            · linarith only [h0, h2, h636, h639, hlam, hphi, u0ehi9, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h641 | h641
              · linarith only [h1, h504, h636, h639, h641, hlam, hphi, u0ehi9, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h643 | h643
                · rcases m.htr 1 3 4 (by decide) (by decide) with h644 | h644
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h645 | h645
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h646 | h646
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h647 | h647
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h648 | h648
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h649 | h649
                            · linarith only [h1, h644, h649, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h1, h641, h643, h644, h648, h649, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h504, h636, h648, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                        · linarith only [h504, h636, h646, h647, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                      · linarith only [h2, h636, h646, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h638, h641, h643, h644, h645, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h1, h637, h639, h643, h644, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h2, h636, h643, hc12, hc23, hlam, hphi]
          · linarith only [h2, h636, h638, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h659 | h659
          · rcases m.htr 1 2 3 (by decide) (by decide) with h660 | h660
            · linarith only [h2, h660, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h662 | h662
              · linarith only [h1, h504, h636, h660, h662, hlam, hphi, u0ehi9, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h664 | h664
                · rcases m.htr 1 3 4 (by decide) (by decide) with h665 | h665
                  · linarith only [h1, h2, h636, h637, h665, hlam, hphi, u0ehi9, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h667 | h667
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                      · linarith only [h2, h636, h637, h668, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                      · linarith only [h2, h636, h668, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h637, h659, h660, h664, h667, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h2, h636, h664, hc12, hc23, hlam, hphi]
          · linarith only [h2, h636, h659, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h674 | h674
        · rcases m.htr 0 3 5 (by decide) (by decide) with h675 | h675
          · rcases m.htr 1 2 3 (by decide) (by decide) with h676 | h676
            · linarith only [h2, h676, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h678 | h678
              · linarith only [h504, h678, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h680 | h680
                · linarith only [h1, h636, h676, h680, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h682 | h682
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h683 | h683
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h684 | h684
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h685 | h685
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h686 | h686
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h687 | h687
                            · linarith only [h1, h682, h687, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · rcases h2bigk with h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h636, h684, h686, hc12, hc23, hlam, hphi, p689_1]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h2, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h504, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h636, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h0, hlam, p689_1]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h676, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h678, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h680, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p689_1, u0ehi6]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                rcases p689_3 (m.d 0 2) (by simp) with h701 | h701
                                · linarith only [h2, h701, hlam]
                                · linarith only [h0, h701, hlam]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h504, hc23, hlam, hphi, ht01, ht12, p689_1, u0ehi6]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h636, hc23, hlam, hphi, ht01, ht12, p689_1, u0ehi6]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht12, p689_1, u0ehi6]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                rcases p689_3 (m.d 0 2) (by simp) with h708 | h708
                                · linarith only [h504, h708, hlam]
                                · linarith only [h0, h708, hlam]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h684, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h636, h684, hc23, hlam, hphi, ht01, ht12, p689_1, u0ehi6]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hc25, hlam, hphi, ht01, ht12, p689_1, u0ehi6]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                rcases p689_3 (m.d 0 2) (by simp) with h715 | h715
                                · linarith only [h636, h715, hlam]
                                · linarith only [h0, h715, hlam]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h685, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h686, hlam, p689_1]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, p689_0]
                          · linarith only [h504, h686, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                        · linarith only [h1, h683, h685, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h2, h684, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                    · linarith only [h1, h675, h682, h683, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h725 | h725
                    · linarith only [h1, h674, h682, h725, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h727 | h727
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h728 | h728
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h729 | h729
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h730 | h730
                            · rcases h2bigk with h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h636, h727, h729, hc12, hc23, hlam, hphi, p731_1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h2, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h504, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h636, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h0, hlam, p731_1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h676, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h678, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h680, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p731_1, u0ehi6]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                rcases p731_3 (m.d 0 2) (by simp) with h743 | h743
                                · linarith only [h2, h743, hlam]
                                · linarith only [h0, h743, hlam]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h1, h504, h674, h676, h725, h730, hc12, hc23, hlam, hphi, p731_1, u0ehi6, u0elo0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h1, h636, h674, h676, h725, h730, hc12, hc23, hlam, hphi, p731_1, u0ehi6, u0elo0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h1, h674, h676, h725, h730, hc12, hc24, hlam, hphi, p731_1, u0ehi6, u0elo0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                rcases p731_3 (m.d 0 2) (by simp) with h750 | h750
                                · linarith only [h504, h750, hlam]
                                · linarith only [h0, h750, hlam]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h727, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h1, h636, h674, h676, h725, h727, h730, hc12, hc23, hlam, hphi, p731_1, u0ehi6, u0elo0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h1, h674, h676, h725, h730, hc12, hc25, hlam, hphi, p731_1, u0ehi6, u0elo0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                rcases p731_3 (m.d 0 2) (by simp) with h757 | h757
                                · linarith only [h636, h757, hlam]
                                · linarith only [h0, h757, hlam]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h728, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h729, hlam, p731_1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hlam, p731_0]
                            · linarith only [h676, h682, h727, h729, h730, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h504, h675, h676, h725, h729, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi6, u0elo0]
                        · linarith only [h1, h2, h675, h728, hlam, hphi, u0ehi6, u0elo0]
                      · linarith only [h1, h2, h675, h676, h725, h727, hc12, hc34, hlam, hphi, ht23, u0ehi6, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h767 | h767
            · linarith only [h2, h767, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h769 | h769
              · linarith only [h504, h769, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h771 | h771
                · linarith only [h1, h636, h767, h771, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h773 | h773
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h774 | h774
                    · linarith only [h1, h675, h774, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h776 | h776
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h777 | h777
                        · linarith only [h504, h674, h675, h777, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h2, h777, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · linarith only [h1, h2, h773, h776, hlam, hphi, u0ehi6, u0elo0]
                  · linarith only [h674, h675, h773, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h782 | h782
          · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
            · linarith only [h2, h783, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h785 | h785
              · linarith only [h504, h785, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h787 | h787
                · linarith only [h1, h636, h783, h787, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h789 | h789
                  · linarith only [h1, h674, h789, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h791 | h791
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h792 | h792
                      · linarith only [h636, h674, h782, h792, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h2, h792, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                    · linarith only [h674, h782, h791, hc13, hc34, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h796 | h796
            · linarith only [h2, h796, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h798 | h798
              · linarith only [h504, h798, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h800 | h800
                · linarith only [h1, h636, h796, h800, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h802 | h802
                  · linarith only [h1, h674, h802, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h804 | h804
                    · linarith only [h1, h2, h782, h804, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h806 | h806
                      · linarith only [h2, h674, h806, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h2, h806, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]

end R2N4
