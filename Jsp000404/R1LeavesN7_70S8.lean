import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_15_M_LI_L_0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h1bigk := hb1.2.2.2
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h4, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h4, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h12, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h12, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
              · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h16, h18, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h0, h20, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h16, h20, h6, hc23, hc34, hlam, hphi]
                · linarith only [h16, h17, h6, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h25, h4, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h16, h27, h4, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                      · rcases h1bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p30_1, u1elo0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          rcases p30_3 (m.d 0 1) (by simp) with h33 | h33
                          · rcases p30_3 (m.d 1 2) (by simp) with h34 | h34
                            · linarith only [h0, h34, hlam]
                            · linarith only [h34, h4, hlam]
                          · linarith only [h33, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h24, hc45, hlam, hphi, ht01, ht0b, ht5b, p30_1, u1elo0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          rcases p30_3 (m.d 0 1) (by simp) with h39 | h39
                          · rcases p30_3 (m.d 1 2) (by simp) with h40 | h40
                            · linarith only [h0, h40, hlam]
                            · linarith only [h40, h5, hlam]
                          · linarith only [h39, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p30_1, u1elo0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h24, hc45, hlam, hphi, ht01, ht0b, ht5b, p30_1, u1elo0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h16, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p30_1, u1elo0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h1, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h4, hlam, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h6, hlam, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h16, hlam, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h2, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p30_1, u1elo0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p30_1, u1elo0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h16, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p30_1, u1elo0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h3, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h5, hlam, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht34, ht45, p30_1, u5elo1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h24, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                      · linarith only [h29, h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                  · linarith only [h4, h6, h65, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                    · linarith only [h0, h16, h4, h67, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
                      · rcases h1bigk with h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h5, h67, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p70_1, u1elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          rcases p70_3 (m.d 0 1) (by simp) with h73 | h73
                          · rcases p70_3 (m.d 1 2) (by simp) with h74 | h74
                            · linarith only [h0, h74, hlam]
                            · linarith only [h4, h74, hlam]
                          · linarith only [h73, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          rcases p70_3 (m.d 0 1) (by simp) with h78 | h78
                          · rcases p70_3 (m.d 1 2) (by simp) with h79 | h79
                            · linarith only [h0, h79, hlam]
                            · linarith only [h24, h5, h67, h69, h79, hc23, hc34, hlam, hphi]
                          · linarith only [h78, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          rcases p70_3 (m.d 0 1) (by simp) with h83 | h83
                          · rcases p70_3 (m.d 1 2) (by simp) with h84 | h84
                            · linarith only [h0, h84, hlam]
                            · linarith only [h5, h84, hlam]
                          · linarith only [h83, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h0, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p70_1, u1elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p70_1, u1elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p70_1, u1elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h1, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h4, hlam, p70_1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h6, hlam, p70_1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h16, hlam, p70_1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h2, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h24, hc12, hlam, hphi, ht23, ht34, ht45, p70_1, u5elo1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p70_1, u1elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h24, hlam, p70_1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h3, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h5, hlam, p70_1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h0, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p70_1, u1elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h0, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p70_1, u1elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, p70_0]
                      · linarith only [h4, h6, h69, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
          · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
            · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
              · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h116 | h116
                      · linarith only [h1, h111, h116, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h113, h116, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h115, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1, h110, h111, h114, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                      · linarith only [h1, h111, h123, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases h1bigk with h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [hlam, p125_0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h110, hc25, hlam, hphi, ht01, ht0b, ht5b, p125_1, u1elo0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h110, h122, h123, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p125_1, u1elo0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          rcases p125_3 (m.d 0 1) (by simp) with h129 | h129
                          · rcases p125_3 (m.d 1 2) (by simp) with h130 | h130
                            · linarith only [h0, h130, hlam]
                            · linarith only [h110, h122, h123, h130, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p125_1, u1elo0]
                          · linarith only [h129, hlam, p125_0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          rcases p125_3 (m.d 0 1) (by simp) with h134 | h134
                          · rcases p125_3 (m.d 1 2) (by simp) with h135 | h135
                            · linarith only [h0, h135, hlam]
                            · linarith only [h110, h135, hlam]
                          · linarith only [h134, hlam, p125_0]
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
                          linarith only [h4, hlam, p125_0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p125_1, u1elo0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h1, h4, hc15, hlam, hphi, ht01, ht0b, ht5b, p125_1, u1elo0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h1, hlam, p125_0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p125_1, u1elo0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [hlam, p125_0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p125_1, u1elo0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h1, h110, h122, h123, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p125_1, u1elo0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h2, hlam, p125_0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h110, h122, h123, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p125_1, u1elo3]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h111, hlam, p125_0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [hlam, p125_0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h113, hlam, p125_1]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h3, hlam, p125_0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h110, hlam, p125_1]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [h112, hlam, p125_0]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [hc14, hlam, hphi, ht45, p125_1, u5elo1]
                        · have p125_0 := h125c.1
                          have p125_1 := h125c.2.1
                          have p125_2 := h125c.2.2.1
                          have p125_3 := h125c.2.2.2
                          linarith only [hlam, p125_0]
                    · linarith only [h122, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1, h110, h111, h121, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h111, h112, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
              · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h166 | h166
                      · rcases h1bigk with h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h110, h165, h166, hc45, hlam, hphi, ht01, ht0b, ht5b, p167_1, u1elo0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h110, h165, h166, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p167_1, u1elo0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h110, h111, h165, h166, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p167_1, u1elo0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          rcases p167_3 (m.d 0 1) (by simp) with h172 | h172
                          · rcases p167_3 (m.d 1 2) (by simp) with h173 | h173
                            · linarith only [h0, h173, hlam]
                            · linarith only [h110, h173, hlam]
                          · linarith only [h172, hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h0, hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h4, hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h111, h4, hlam, p167_1]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h111, h164, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p167_1]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h1, hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h111, h164, hc12, hc23, hlam, hphi, p167_1]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h111, hlam, p167_1]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h110, h111, h164, h165, h166, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p167_1]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h2, hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h110, h165, h166, hc45, hlam, hphi, ht01, ht0b, ht5b, p167_1, u1elo3]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p167_1, u1elo0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h110, h165, h166, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p167_1, u1elo0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h3, hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h110, hlam, p167_1]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h162, hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [h163, hlam, p167_0]
                        · have p167_0 := h167c.1
                          have p167_1 := h167c.2.1
                          have p167_2 := h167c.2.2.1
                          have p167_3 := h167c.2.2.2
                          linarith only [hlam, p167_0]
                      · linarith only [h110, h111, h165, h166, h4, hc35, hlam, hphi, u5elo4]
                    · linarith only [h165, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h200 | h200
                      · rcases h1bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h110, h199, h200, hc45, hlam, hphi, ht01, ht0b, ht5b, p201_1, u1elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h110, h199, h200, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p201_1, u1elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h110, h111, h199, h200, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p201_1, u1elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          rcases p201_3 (m.d 0 1) (by simp) with h206 | h206
                          · rcases p201_3 (m.d 1 2) (by simp) with h207 | h207
                            · linarith only [h0, h207, hlam]
                            · linarith only [h110, h207, hlam]
                          · linarith only [h206, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h0, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h4, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h111, h4, hlam, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h0, h110, h199, h200, hc45, hlam, hphi, ht01, ht0b, ht5b, p201_1, u1elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h1, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p201_1, u1elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h111, hlam, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h110, h111, h199, h2, h200, hc45, hlam, hphi, ht01, ht0b, ht5b, p201_1, u1elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h2, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h110, h199, h2, h200, hc45, hlam, hphi, ht01, ht0b, ht5b, p201_1, u1elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h110, h164, h199, h2, h200, h4, hc13, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p201_1, u1elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h110, h199, h2, h200, hc45, hlam, hphi, ht01, ht0b, ht5b, p201_1, u1elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h3, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h110, hlam, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h162, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h163, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                      · linarith only [h164, h200, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h110, h199, h4, hc25, hlam, hphi, u5elo3]
                · linarith only [h110, h111, h163, h4, hc25, hlam, hphi, u5elo4]
              · linarith only [h110, h162, h4, hc25, hlam, hphi, u5elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
            · rcases m.htr 1 3 5 (by decide) (by decide) with h236 | h236
              · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                · rcases m.htr 2 3 4 (by decide) (by decide) with h238 | h238
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h239 | h239
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h240 | h240
                      · linarith only [h1, h235, h240, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h2, h237, h240, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1, h236, h239, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1, h235, h238, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                      · linarith only [h1, h235, h247, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases h1bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          rcases p249_3 (m.d 0 1) (by simp) with h251 | h251
                          · rcases p249_3 (m.d 1 2) (by simp) with h252 | h252
                            · linarith only [h252, hlam, p249_0]
                            · rcases p249_3 (m.d 1 3) (by simp) with h254 | h254
                              · linarith only [h1, h254, hlam]
                              · linarith only [h254, h4, hlam]
                          · linarith only [h251, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h236, h247, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          rcases p249_3 (m.d 0 1) (by simp) with h259 | h259
                          · rcases p249_3 (m.d 1 2) (by simp) with h260 | h260
                            · linarith only [h0, h260, hlam]
                            · rcases p249_3 (m.d 1 3) (by simp) with h262 | h262
                              · linarith only [h1, h262, hlam]
                              · linarith only [h235, h262, hlam]
                          · linarith only [h259, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          rcases p249_3 (m.d 0 1) (by simp) with h266 | h266
                          · rcases p249_3 (m.d 1 2) (by simp) with h267 | h267
                            · linarith only [h0, h267, hlam]
                            · rcases p249_3 (m.d 1 3) (by simp) with h269 | h269
                              · linarith only [h1, h269, hlam]
                              · linarith only [h236, h269, hlam]
                          · linarith only [h266, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h0, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h4, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h110, hc14, hlam, hphi, ht45, p249_1, u5elo2]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h110, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h1, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h2, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h235, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h237, hlam, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h3, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p249_1, u5elo1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h236, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h1, h236, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                    · linarith only [h246, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h235, h245, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · linarith only [h235, h236, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h296 | h296
              · rcases m.htr 1 4 5 (by decide) (by decide) with h297 | h297
                · rcases m.htr 2 3 4 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h300 | h300
                      · rcases h1bigk with h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          rcases p301_3 (m.d 0 1) (by simp) with h303 | h303
                          · rcases p301_3 (m.d 1 2) (by simp) with h304 | h304
                            · linarith only [h304, hlam, p301_0]
                            · rcases p301_3 (m.d 1 3) (by simp) with h306 | h306
                              · linarith only [h1, h306, hlam]
                              · linarith only [h306, h4, hlam]
                          · linarith only [h303, hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h296, h300, hc45, hlam, hphi, ht01, ht0b, ht5b, p301_1, u1elo0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h235, h296, h300, hc45, hlam, hphi, ht01, ht0b, ht5b, p301_1, u1elo0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          rcases p301_3 (m.d 0 1) (by simp) with h312 | h312
                          · rcases p301_3 (m.d 1 2) (by simp) with h313 | h313
                            · linarith only [h0, h313, hlam]
                            · rcases p301_3 (m.d 1 3) (by simp) with h315 | h315
                              · linarith only [h1, h315, hlam]
                              · linarith only [h296, h315, hlam]
                          · linarith only [h312, hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h0, hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h4, hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h235, h296, h300, hc45, hlam, hphi, ht01, ht0b, ht5b, p301_1, u1elo1]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h110, hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h1, hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h235, h298, hc12, hc23, hlam, hphi, p301_1]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h235, hlam, p301_1]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h235, h298, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p301_1]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h2, hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p301_1, u1elo0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p301_1, u1elo0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h110, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p301_1, u1elo0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h3, hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p301_1, u5elo1]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h296, hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [h297, hlam, p301_0]
                        · have p301_0 := h301c.1
                          have p301_1 := h301c.2.1
                          have p301_2 := h301c.2.2.1
                          have p301_3 := h301c.2.2.2
                          linarith only [hlam, p301_0]
                      · linarith only [h235, h300, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h235, h296, h298, h299, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h341 | h341
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h342 | h342
                      · rcases h1bigk with h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          rcases p343_3 (m.d 0 1) (by simp) with h345 | h345
                          · rcases p343_3 (m.d 1 2) (by simp) with h346 | h346
                            · linarith only [h346, hlam, p343_0]
                            · rcases p343_3 (m.d 1 3) (by simp) with h348 | h348
                              · linarith only [h1, h348, hlam]
                              · linarith only [h348, h4, hlam]
                          · linarith only [h345, hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h296, h342, hc45, hlam, hphi, ht01, ht0b, ht5b, p343_1, u1elo0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h235, h296, h342, hc45, hlam, hphi, ht01, ht0b, ht5b, p343_1, u1elo0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          rcases p343_3 (m.d 0 1) (by simp) with h354 | h354
                          · rcases p343_3 (m.d 1 2) (by simp) with h355 | h355
                            · linarith only [h0, h355, hlam]
                            · rcases p343_3 (m.d 1 3) (by simp) with h357 | h357
                              · linarith only [h1, h357, hlam]
                              · linarith only [h296, h357, hlam]
                          · linarith only [h354, hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h0, hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h4, hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h235, h296, h342, hc45, hlam, hphi, ht01, ht0b, ht5b, p343_1, u1elo1]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h110, hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h1, hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p343_1, u1elo0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h235, hlam, p343_1]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h2, h235, hc15, hlam, hphi, ht01, ht0b, ht5b, p343_1, u1elo0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h2, hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p343_1, u1elo0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p343_1, u1elo0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h110, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p343_1, u1elo0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h3, hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p343_1, u5elo1]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h296, hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [h297, hlam, p343_0]
                        · have p343_0 := h343c.1
                          have p343_1 := h343c.2.1
                          have p343_2 := h343c.2.2.1
                          have p343_3 := h343c.2.2.2
                          linarith only [hlam, p343_0]
                      · linarith only [h298, h342, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h341, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h235, h296, h297, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h384 | h384
                · rcases m.htr 2 3 4 (by decide) (by decide) with h385 | h385
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h386 | h386
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h387 | h387
                      · rcases h1bigk with h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          rcases p388_3 (m.d 0 1) (by simp) with h390 | h390
                          · rcases p388_3 (m.d 1 2) (by simp) with h391 | h391
                            · linarith only [h391, hlam, p388_0]
                            · rcases p388_3 (m.d 1 3) (by simp) with h393 | h393
                              · linarith only [h1, h393, hlam]
                              · linarith only [h393, h4, hlam]
                          · linarith only [h390, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          rcases p388_3 (m.d 0 1) (by simp) with h397 | h397
                          · rcases p388_3 (m.d 1 2) (by simp) with h398 | h398
                            · linarith only [h0, h398, hlam]
                            · rcases p388_3 (m.d 1 3) (by simp) with h400 | h400
                              · linarith only [h400, hlam, p388_0]
                              · rcases p388_3 (m.d 1 4) (by simp) with h402 | h402
                                · linarith only [h2, h402, hlam]
                                · linarith only [h235, h402, hlam]
                          · linarith only [h397, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h384, hc45, hlam, hphi, ht01, ht0b, ht5b, p388_1, u1elo0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          rcases p388_3 (m.d 0 1) (by simp) with h407 | h407
                          · rcases p388_3 (m.d 1 2) (by simp) with h408 | h408
                            · linarith only [h0, h408, hlam]
                            · rcases p388_3 (m.d 1 3) (by simp) with h410 | h410
                              · linarith only [h1, h410, hlam]
                              · rcases p388_3 (m.d 1 4) (by simp) with h412 | h412
                                · linarith only [h2, h412, hlam]
                                · linarith only [h384, h412, hlam]
                          · linarith only [h407, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h0, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h4, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h384, hc45, hlam, hphi, ht01, ht0b, ht5b, p388_1, u1elo1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h110, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h1, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h296, h385, h387, hc12, hc23, hlam, hphi, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h235, hlam, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h296, hlam, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h2, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p388_1, u1elo0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p388_1, u1elo0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h2, h296, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p388_1, u1elo0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h3, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p388_1, u5elo1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h3, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p388_1, u1elo0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h384, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hlam, p388_0]
                      · linarith only [h235, h387, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h386, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h438 | h438
                    · linarith only [h296, h385, h4, h438, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h4, h438, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h441 | h441
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h442 | h442
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h443 | h443
                      · linarith only [h235, h384, h4, h441, h443, hc12, hc23, hlam, hphi]
                      · linarith only [h235, h4, h443, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h4, h442, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h447 | h447
                    · linarith only [h296, h4, h441, h447, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h4, h447, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h451 | h451
      · rcases m.htr 1 2 3 (by decide) (by decide) with h452 | h452
        · linarith only [h0, h2, h452, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h454 | h454
          · linarith only [h1, h2, h452, h454, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h456 | h456
            · linarith only [h1, h2, h456, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h458 | h458
              · linarith only [h1, h2, h458, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h460 | h460
                · rcases m.htr 2 3 4 (by decide) (by decide) with h461 | h461
                  · linarith only [h2, h451, h452, h456, h458, h461, hc12, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h463 | h463
                    · linarith only [h452, h458, h461, h463, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h452, h463, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h2, h451, h458, h460, hc13, hc45, hlam, hphi, ht34]
      · linarith only [h0, h451, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h468 | h468
    · rcases m.htr 0 1 5 (by decide) (by decide) with h469 | h469
      · rcases m.htr 1 2 3 (by decide) (by decide) with h470 | h470
        · linarith only [h0, h1, h470, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
          · linarith only [h0, h1, h472, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h474 | h474
            · rcases m.htr 1 3 5 (by decide) (by decide) with h475 | h475
              · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                · linarith only [h1, h468, h476, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h478 | h478
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h479 | h479
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h480 | h480
                      · linarith only [h474, h476, h480, hlam]
                      · rcases h1bigk with h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p482_1, u1elo2]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h1, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p482_1, u1elo2]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p482_1, u1elo2]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h0, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h470, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h472, h474, hc34, hlam, hphi, ht45, p482_1, u5elo1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h472, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hc01, hlam, hphi, p482_1, u1elo2]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          rcases p482_3 (m.d 0 1) (by simp) with h494 | h494
                          · linarith only [h1, h494, hlam]
                          · linarith only [h0, h494, hlam]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          rcases p482_3 (m.d 0 1) (by simp) with h498 | h498
                          · linarith only [h1, h498, hlam]
                          · linarith only [h468, h498, hlam]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          rcases p482_3 (m.d 0 1) (by simp) with h501 | h501
                          · linarith only [h1, h501, hlam]
                          · linarith only [h469, h501, hlam]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h468, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h476, hc12, hc45, hlam, hphi, ht23, ht34, p482_1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h474, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h476, hlam, p482_1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h469, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h469, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p482_1, u1elo0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h475, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h1, h469, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p482_1, u1elo2]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                    · linarith only [h1, h470, h479, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1, h469, h470, h472, h474, h478, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
              · linarith only [h1, h469, h472, h475, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1, h469, h472, h474, hc12, hc34, hlam, hphi, ht23]
      · linarith only [h468, h469, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h519 | h519
      · rcases m.htr 1 2 3 (by decide) (by decide) with h520 | h520
        · linarith only [h0, h1, h520, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h522 | h522
          · linarith only [h0, h1, h522, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h524 | h524
            · rcases m.htr 1 3 5 (by decide) (by decide) with h525 | h525
              · rcases m.htr 1 4 5 (by decide) (by decide) with h526 | h526
                · rcases m.htr 2 3 4 (by decide) (by decide) with h527 | h527
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h528 | h528
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h529 | h529
                      · rcases h1bigk with h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h468, h524, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p530_1, u1elo2]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h1, hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h468, hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h468, h524, hc15, hlam, hphi, ht01, ht0b, ht5b, p530_1, u1elo2]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h0, hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h520, hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h468, hc01, hlam, hphi, p530_1, u1elo1]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h522, hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p530_1, u1elo2]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          rcases p530_3 (m.d 0 1) (by simp) with h542 | h542
                          · linarith only [h1, h542, hlam]
                          · linarith only [h0, h542, hlam]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h468, h519, h522, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p530_1, u1elo2]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          rcases p530_3 (m.d 0 1) (by simp) with h547 | h547
                          · linarith only [h1, h547, hlam]
                          · linarith only [h519, h547, hlam]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h519, h522, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p530_1, u1elo3]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          rcases p530_3 (m.d 0 1) (by simp) with h551 | h551
                          · linarith only [h468, h551, hlam]
                          · linarith only [h0, h551, hlam]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h524, hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          rcases p530_3 (m.d 0 1) (by simp) with h556 | h556
                          · linarith only [h468, h556, hlam]
                          · linarith only [h519, h556, hlam]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h519, hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h519, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p530_1, u1elo0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h525, hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [h526, hlam, p530_0]
                        · have p530_0 := h530c.1
                          have p530_1 := h530c.2.1
                          have p530_2 := h530c.2.2.1
                          have p530_3 := h530c.2.2.2
                          linarith only [hlam, p530_0]
                      · linarith only [h468, h519, h524, h526, h529, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · linarith only [h468, h520, h524, h528, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h468, h520, h524, h527, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h468, h519, h522, h526, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h468, h519, h522, h524, h525, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1, h519, h522, h524, hc12, hc34, hlam, hphi, ht23]
      · linarith only [h0, h519, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

end R2N4
