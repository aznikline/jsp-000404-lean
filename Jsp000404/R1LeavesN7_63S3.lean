import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
  · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
    · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
      · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
        · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
          · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
            · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
              · linarith only [h0, h10, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h0, h10, h4, h7, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h8, h9, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
            · linarith only [h0, h14, h4, h8, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h16, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h0, h16, h4, h7, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
          · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
            · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
              · linarith only [h21, h4, h7, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                · linarith only [h19, h23, h4, h7, hlam]
                · rcases h5bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hc15, hlam, hphi, p25_1, u5elo0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hc25, hlam, hphi, p25_1, u5elo0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hc35, hlam, hphi, p25_1, u5elo0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h19, h4, h7, hc34, hlam, hphi, ht45, p25_1, u5elo0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h2, hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h19, h21, hc34, hlam, hphi, ht45, p25_1, u5elo1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h0, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p25_1, u1elo0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h7, hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hc05, hlam, hphi, p25_1, u5elo2]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h5, hlam, p25_1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h0, h23, h5, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25_1, u1elo0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h21, hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h19, h20, h3, h4, h7, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p25_1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h6, hlam, p25_1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h20, hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h23, hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h3, hlam, p25_1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h3, hc15, hlam, hphi, p25_1, u5elo0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h1, h20, h3, hc35, hlam, hphi, ht01, ht0b, ht5b, p25_1, u1elo0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h1, h3, hc35, hlam, hphi, ht01, ht0b, ht5b, p25_1, u1elo0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hlam, p25_0]
            · linarith only [h19, h20, h6, hc34, hlam, hphi, ht45, u5elo1]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
            · linarith only [h0, h19, h4, h52, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
              · linarith only [h4, h54, h7, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                · linarith only [h56, h6, h7, hlam]
                · linarith only [h1, h19, h3, h56, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
        · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
          · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
            · linarith only [h0, h5, h6, h61, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h60, h61, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
            · linarith only [h6, h60, h64, hc13, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
              · linarith only [h0, h4, h66, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h1, h59, h66, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
          · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
            · linarith only [h5, h6, h70, hlam]
            · linarith only [h69, h70, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
            · linarith only [h0, h4, h69, h73, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
              · linarith only [h0, h4, h75, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                · rcases h5bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc15, hlam, hphi, p78_1, u5elo0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h69, h75, hc23, hlam, hphi, ht34, ht45, p78_1, u5elo0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc35, hlam, hphi, p78_1, u5elo0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h4, h59, h69, hc23, hlam, hphi, ht34, ht45, p78_1, u5elo0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h2, hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h69, h75, hc23, hlam, hphi, ht34, ht45, p78_1, u5elo1]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h6, hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h59, hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc05, hlam, hphi, p78_1, u5elo2]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h5, hlam, p78_1]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h73, hlam, p78_1]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h75, hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h3, h4, h59, h69, hc23, hc35, hlam, hphi, p78_1]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc15, hlam, hphi, p78_1, u5elo3]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc25, hlam, hphi, p78_1, u5elo3]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h4, h59, h69, hc23, hlam, hphi, ht34, ht45, p78_1, u5elo3]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h3, hlam, p78_1]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h1, h3, h4, h59, h69, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p78_1, u1elo0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h1, h3, h69, h75, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p78_1, u1elo0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h77, hlam, p78_1]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hlam, p78_0]
                · linarith only [h1, h3, h69, h77, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · linarith only [h4, h5, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h106 | h106
    · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
      · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
        · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
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
                    linarith only [h106, h110, h112, hc45, hlam, hphi, p113_1, u5elo0]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h110, h112, hc45, hlam, hphi, p113_1, u5elo0]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h112, hc45, hlam, hphi, p113_1, u5elo0]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [hc45, hlam, hphi, p113_1, u5elo0]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h2, hlam, p113_0]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [hlam, p113_0]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h110, h112, hc45, hlam, hphi, p113_1, u5elo1]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h112, hc45, hlam, hphi, p113_1, u5elo1]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h1, h106, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p113_1, u1elo0]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [hc05, hlam, hphi, p113_1, u5elo2]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h106, hlam, p113_1]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [hlam, p113_0]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h112, hc45, hlam, hphi, p113_1, u5elo2]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h1, h106, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p113_1, u1elo0]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [hc05, hlam, hphi, p113_1, u5elo3]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h107, hlam, p113_1]
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
                    linarith only [h1, h106, h110, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p113_1, u1elo0]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h3, hlam, p113_1]
                  · have p113_0 := h113c.1
                    have p113_1 := h113c.2.1
                    have p113_2 := h113c.2.2.1
                    have p113_3 := h113c.2.2.2
                    linarith only [h108, hlam, p113_1]
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
                · linarith only [h1, h108, h112, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h108, h111, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h106, h109, h110, h4, hc25, hlam, hphi, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
            · rcases m.htr 2 4 5 (by decide) (by decide) with h143 | h143
              · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
                · rcases h5bigk with h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hc15, hlam, hphi, p145_1, u5elo0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h142, h144, hc45, hlam, hphi, p145_1, u5elo0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h144, hc45, hlam, hphi, p145_1, u5elo0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hc45, hlam, hphi, p145_1, u5elo0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h2, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h142, h144, hc45, hlam, hphi, p145_1, u5elo1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h144, hc45, hlam, hphi, p145_1, u5elo1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h1, h106, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p145_1, u1elo0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hc05, hlam, hphi, p145_1, u5elo2]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h106, hlam, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h144, hc45, hlam, hphi, p145_1, u5elo2]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h1, h106, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p145_1, u1elo0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hc05, hlam, hphi, p145_1, u5elo3]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h107, hlam, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h142, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h106, h142, h2, hc45, hlam, hphi, p145_1, u5elo0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h3, hlam, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h108, hlam, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h143, hlam, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h144, hlam, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hlam, p145_0]
                · linarith only [h109, h144, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h1, h106, h108, h142, h143, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
              · rcases m.htr 3 4 5 (by decide) (by decide) with h174 | h174
                · rcases h5bigk with h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [hlam, p175_0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h107, h142, hc23, hlam, hphi, ht34, ht45, p175_1, u5elo0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [hc25, hlam, hphi, p175_1, u5elo0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h142, hc23, hlam, hphi, ht34, ht45, p175_1, u5elo0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [hc45, hlam, hphi, p175_1, u5elo0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h2, hlam, p175_0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [hlam, p175_0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h106, h109, h142, h4, hc23, hc34, hlam, hphi, p175_1]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h1, h106, h142, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p175_1, u1elo0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h1, h106, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p175_1, u1elo0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [hc05, hlam, hphi, p175_1, u5elo2]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h106, hlam, p175_1]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [hlam, p175_0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h142, hlam, p175_1]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [hc45, hlam, hphi, p175_1, u5elo2]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [hc05, hlam, hphi, p175_1, u5elo3]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h107, hlam, p175_1]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h1, h106, h107, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, p175_1, u1elo0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [hlam, p175_0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h1, h106, h107, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p175_1, u1elo0]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h3, hlam, p175_1]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h108, hlam, p175_1]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h173, hlam, p175_1]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [h174, hlam, p175_1]
                  · have p175_0 := h175c.1
                    have p175_1 := h175c.2.1
                    have p175_2 := h175c.2.2.1
                    have p175_3 := h175c.2.2.2
                    linarith only [hlam, p175_0]
                · linarith only [h1, h106, h107, h109, h142, h174, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1, h106, h107, h108, h142, h173, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · linarith only [h1, h106, h108, h3, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h204 | h204
        · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
          · rcases m.htr 2 3 5 (by decide) (by decide) with h206 | h206
            · linarith only [h0, h106, h107, h206, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h205, h206, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
            · linarith only [h107, h205, h209, hc13, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h211 | h211
              · rcases m.htr 3 4 5 (by decide) (by decide) with h212 | h212
                · rcases h5bigk with h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hlam, p213_0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hc15, hlam, hphi, p213_1, u5elo0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hc25, hlam, hphi, p213_1, u5elo0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h107, hc13, hlam, hphi, ht34, ht45, p213_1, u5elo0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hc45, hlam, hphi, p213_1, u5elo0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h2, hlam, p213_0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hlam, p213_0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h209, hc23, hlam, hphi, ht34, ht45, p213_1, u5elo1]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h107, hlam, p213_0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h1, h106, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p213_1, u1elo0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hc05, hlam, hphi, p213_1, u5elo2]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h106, hlam, p213_1]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hlam, p213_0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h209, hlam, p213_1]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h1, h106, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p213_1, u1elo0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hc05, hlam, hphi, p213_1, u5elo3]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h106, hc25, hlam, hphi, p213_1, u5elo3]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hc25, hlam, hphi, p213_1, u5elo3]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hlam, p213_0]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hc45, hlam, hphi, p213_1, u5elo3]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h3, hlam, p213_1]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h204, hlam, p213_1]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h211, hlam, p213_1]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [h212, hlam, p213_1]
                  · have p213_0 := h213c.1
                    have p213_1 := h213c.2.1
                    have p213_2 := h213c.2.2.1
                    have p213_3 := h213c.2.2.2
                    linarith only [hlam, p213_0]
                · linarith only [h1, h204, h212, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h204, h211, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
        · linarith only [h1, h106, h204, h3, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
      · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
        · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
          · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
            · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
              · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                · rcases h5bigk with h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hlam, p248_0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h106, hc12, hlam, hphi, ht23, ht34, ht45, p248_1, u5elo0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h106, hc12, hlam, hphi, ht23, ht34, ht45, p248_1, u5elo0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hc35, hlam, hphi, p248_1, u5elo0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hc45, hlam, hphi, p248_1, u5elo0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h2, hlam, p248_0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hlam, p248_0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h106, hlam, p248_0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hc35, hlam, hphi, p248_1, u5elo1]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hc45, hlam, hphi, p248_1, u5elo1]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hc05, hlam, hphi, p248_1, u5elo2]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hc15, hlam, hphi, p248_1, u5elo2]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hlam, p248_0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h247, hc45, hlam, hphi, p248_1, u5elo2]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hc45, hlam, hphi, p248_1, u5elo2]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h106, h2, hc12, hlam, hphi, ht23, ht34, ht45, p248_1, u5elo3]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h242, hlam, p248_1]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h245, hlam, p248_0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hlam, p248_0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h2, h242, hc45, hlam, hphi, p248_1, u5elo0]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h3, hlam, p248_1]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h243, hlam, p248_1]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h246, hlam, p248_1]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [h247, hlam, p248_1]
                  · have p248_0 := h248c.1
                    have p248_1 := h248c.2.1
                    have p248_2 := h248c.2.2.1
                    have p248_3 := h248c.2.2.2
                    linarith only [hlam, p248_0]
                · linarith only [h1, h243, h247, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h243, h246, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h1, h242, h243, h244, h245, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
            · rcases m.htr 2 4 5 (by decide) (by decide) with h278 | h278
              · rcases m.htr 3 4 5 (by decide) (by decide) with h279 | h279
                · rcases h5bigk with h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hlam, p280_0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hc15, hlam, hphi, p280_1, u5elo0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hc25, hlam, hphi, p280_1, u5elo0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hc35, hlam, hphi, p280_1, u5elo0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hc45, hlam, hphi, p280_1, u5elo0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h2, hlam, p280_0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hlam, p280_0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h106, hlam, p280_0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h279, hc45, hlam, hphi, p280_1, u5elo1]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h1, h243, hc45, hlam, hphi, ht01, ht0b, ht5b, p280_1, u1elo0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hc05, hlam, hphi, p280_1, u5elo2]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hc15, hlam, hphi, p280_1, u5elo2]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hlam, p280_0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h279, hc45, hlam, hphi, p280_1, u5elo2]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hc45, hlam, hphi, p280_1, u5elo2]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h106, h2, hc12, hlam, hphi, ht23, ht34, ht45, p280_1, u5elo3]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h242, hlam, p280_1]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h277, hlam, p280_0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hlam, p280_0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h2, h242, hc45, hlam, hphi, p280_1, u5elo0]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h3, hlam, p280_1]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h243, hlam, p280_1]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h278, hlam, p280_1]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [h279, hlam, p280_1]
                  · have p280_0 := h280c.1
                    have p280_1 := h280c.2.1
                    have p280_2 := h280c.2.2.1
                    have p280_3 := h280c.2.2.2
                    linarith only [hlam, p280_0]
                · linarith only [h244, h279, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h1, h243, h244, h278, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h106, h242, h277, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
          · rcases m.htr 2 3 5 (by decide) (by decide) with h310 | h310
            · rcases m.htr 2 4 5 (by decide) (by decide) with h311 | h311
              · rcases m.htr 3 4 5 (by decide) (by decide) with h312 | h312
                · linarith only [h243, h309, h312, h4, hc12, hc23, hlam, hphi]
                · rcases h5bigk with h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [hlam, p314_0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [hc15, hlam, hphi, p314_1, u5elo0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h243, h311, h4, hc12, hlam, hphi, ht23, ht34, ht45, p314_1, u5elo0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h312, hc34, hlam, hphi, ht45, p314_1, u5elo0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h243, h4, hc12, hlam, hphi, ht23, ht34, ht45, p314_1, u5elo0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h2, hlam, p314_0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [hlam, p314_0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h106, hlam, p314_0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h312, hc34, hlam, hphi, ht45, p314_1, u5elo1]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h243, hlam, p314_0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [hc05, hlam, hphi, p314_1, u5elo2]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [hc15, hlam, hphi, p314_1, u5elo2]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [hlam, p314_0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h312, hc34, hlam, hphi, ht45, p314_1, u5elo2]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [hc45, hlam, hphi, p314_1, u5elo2]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h243, h3, h4, hc12, hc35, hlam, hphi, ht23, p314_1]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h242, hlam, p314_1]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h310, hlam, p314_0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [hlam, p314_0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h312, hlam, p314_0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h3, hlam, p314_1]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h243, h311, h4, hc12, hc24, hlam, hphi, p314_1]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h311, hlam, p314_1]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [h1, h3, hc35, hlam, hphi, ht01, ht0b, ht5b, p314_1, u1elo0]
                  · have p314_0 := h314c.1
                    have p314_1 := h314c.2.1
                    have p314_2 := h314c.2.2.1
                    have p314_3 := h314c.2.2.2
                    linarith only [hlam, p314_0]
              · linarith only [h1, h3, h311, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h242, h309, h310, hc34, hlam, hphi, ht45, u5elo1]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h342 | h342
            · rcases m.htr 2 4 5 (by decide) (by decide) with h343 | h343
              · rcases m.htr 3 4 5 (by decide) (by decide) with h344 | h344
                · linarith only [h242, h243, h344, hlam]
                · linarith only [h309, h342, h343, h344, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h1, h3, h343, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h106, h242, h342, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h349 | h349
        · rcases m.htr 2 3 4 (by decide) (by decide) with h350 | h350
          · rcases m.htr 2 3 5 (by decide) (by decide) with h351 | h351
            · rcases m.htr 2 4 5 (by decide) (by decide) with h352 | h352
              · rcases m.htr 3 4 5 (by decide) (by decide) with h353 | h353
                · rcases h5bigk with h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hlam, p354_0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hc15, hlam, hphi, p354_1, u5elo0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h242, h351, hc13, hlam, hphi, ht34, ht45, p354_1, u5elo0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h242, hc13, hlam, hphi, ht34, ht45, p354_1, u5elo0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hc45, hlam, hphi, p354_1, u5elo0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h2, hlam, p354_0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hlam, p354_0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h106, hlam, p354_0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h242, hlam, p354_0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hc45, hlam, hphi, p354_1, u5elo1]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hc05, hlam, hphi, p354_1, u5elo2]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hc15, hlam, hphi, p354_1, u5elo2]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hlam, p354_0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h242, hc13, hlam, hphi, ht34, ht45, p354_1, u5elo2]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hc45, hlam, hphi, p354_1, u5elo2]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h106, h2, hc12, hlam, hphi, ht23, ht34, ht45, p354_1, u5elo3]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h106, hc12, hlam, hphi, ht23, ht34, ht45, p354_1, u5elo3]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h351, hlam, p354_0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hlam, p354_0]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h351, hc45, hlam, hphi, p354_1, u5elo2]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h3, hlam, p354_1]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h349, hlam, p354_1]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h352, hlam, p354_1]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [h353, hlam, p354_1]
                  · have p354_0 := h354c.1
                    have p354_1 := h354c.2.1
                    have p354_2 := h354c.2.2.1
                    have p354_3 := h354c.2.2.2
                    linarith only [hlam, p354_0]
                · linarith only [h1, h349, h353, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h349, h352, h4, hlam]
            · linarith only [h350, h351, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h383 | h383
            · linarith only [h242, h350, h383, hc13, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h385 | h385
              · rcases m.htr 3 4 5 (by decide) (by decide) with h386 | h386
                · rcases h5bigk with h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hlam, p387_0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hc15, hlam, hphi, p387_1, u5elo0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h106, hc12, hlam, hphi, ht23, ht34, ht45, p387_1, u5elo0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h106, h383, hc12, hlam, hphi, ht23, ht34, ht45, p387_1, u5elo0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hc45, hlam, hphi, p387_1, u5elo0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h2, hlam, p387_0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hlam, p387_0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h106, hlam, p387_0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h242, hlam, p387_0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hc45, hlam, hphi, p387_1, u5elo1]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hc05, hlam, hphi, p387_1, u5elo2]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hc15, hlam, hphi, p387_1, u5elo2]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hlam, p387_0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h383, hlam, p387_1]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h383, hc45, hlam, hphi, p387_1, u5elo3]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h106, h2, hc12, hlam, hphi, ht23, ht34, ht45, p387_1, u5elo3]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h106, hc12, hlam, hphi, ht23, ht34, ht45, p387_1, u5elo3]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hc25, hlam, hphi, p387_1, u5elo3]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hlam, p387_0]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hc45, hlam, hphi, p387_1, u5elo3]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h3, hlam, p387_1]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h349, hlam, p387_1]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h385, hlam, p387_1]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [h386, hlam, p387_1]
                  · have p387_0 := h387c.1
                    have p387_1 := h387c.2.1
                    have p387_2 := h387c.2.2.1
                    have p387_3 := h387c.2.2.2
                    linarith only [hlam, p387_0]
                · linarith only [h1, h349, h386, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h349, h385, h4, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
          · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
            · rcases m.htr 2 4 5 (by decide) (by decide) with h417 | h417
              · rcases m.htr 3 4 5 (by decide) (by decide) with h418 | h418
                · linarith only [h349, h4, h415, h418, hc12, hc23, hlam, hphi]
                · rcases h5bigk with h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [hlam, p420_0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [hc15, hlam, hphi, p420_1, u5elo0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [hc25, hlam, hphi, p420_1, u5elo0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [hc35, hlam, hphi, p420_1, u5elo0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h349, h4, hc12, hlam, hphi, ht23, ht34, ht45, p420_1, u5elo0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h2, hlam, p420_0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [hlam, p420_0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h106, hlam, p420_0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h242, hlam, p420_0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h349, hlam, p420_0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [hc05, hlam, hphi, p420_1, u5elo2]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h349, h4, hc12, hlam, hphi, ht23, ht34, ht45, p420_1, u5elo2]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [hlam, p420_0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h242, hc13, hlam, hphi, ht34, ht45, p420_1, u5elo2]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h349, h4, hc12, hlam, hphi, ht23, ht34, ht45, p420_1, u5elo2]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h3, h349, h4, hc12, hc35, hlam, hphi, ht23, p420_1]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h349, h4, hc12, hlam, hphi, ht23, ht34, ht45, p420_1, u5elo3]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h416, hlam, p420_0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [hlam, p420_0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h418, hlam, p420_0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h3, hlam, p420_1]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h349, h4, h417, hc12, hc24, hlam, hphi, p420_1]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h417, hlam, p420_1]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [h1, h3, hc35, hlam, hphi, ht01, ht0b, ht5b, p420_1, u1elo0]
                  · have p420_0 := h420c.1
                    have p420_1 := h420c.2.1
                    have p420_2 := h420c.2.2.1
                    have p420_3 := h420c.2.2.2
                    linarith only [hlam, p420_0]
              · linarith only [h1, h3, h4, h417, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h415, h416, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
            · linarith only [h242, h415, h448, hc13, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h450 | h450
              · rcases m.htr 3 4 5 (by decide) (by decide) with h451 | h451
                · rcases h5bigk with h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [hlam, p452_0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h349, h4, hc12, hlam, hphi, ht23, ht34, ht45, p452_1, u5elo0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [hc25, hlam, hphi, p452_1, u5elo0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h448, hc23, hlam, hphi, ht34, ht45, p452_1, u5elo0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [hc45, hlam, hphi, p452_1, u5elo0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h2, hlam, p452_0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [hlam, p452_0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h106, hlam, p452_0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h242, hlam, p452_0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h349, hlam, p452_0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [hc05, hlam, hphi, p452_1, u5elo2]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h349, h4, h448, hc12, hlam, hphi, ht23, ht34, ht45, p452_1, u5elo3]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [hlam, p452_0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h448, hlam, p452_1]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h349, h4, h448, hc12, hlam, hphi, ht23, ht34, ht45, p452_1, u5elo3]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h3, h349, h4, hc12, hlam, hphi, ht23, ht34, ht45, p452_1, u5elo3]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h349, h4, hc12, hlam, hphi, ht23, ht34, ht45, p452_1, u5elo3]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [hc25, hlam, hphi, p452_1, u5elo3]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [hlam, p452_0]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h349, h4, hc12, hlam, hphi, ht23, ht34, ht45, p452_1, u5elo3]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h3, hlam, p452_1]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h349, h4, h450, hc12, hc24, hlam, hphi, p452_1]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h450, hlam, p452_1]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [h451, hlam, p452_1]
                  · have p452_0 := h452c.1
                    have p452_1 := h452c.2.1
                    have p452_2 := h452c.2.2.1
                    have p452_3 := h452c.2.2.2
                    linarith only [hlam, p452_0]
                · linarith only [h1, h3, h4, h415, h451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1, h3, h4, h450, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]

end R2N4
