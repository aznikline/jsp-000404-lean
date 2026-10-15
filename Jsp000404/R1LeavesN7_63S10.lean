import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h0, h14, h8, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h0, h12, h14, h8, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h10, h13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                    · linarith only [h12, h19, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h12, h18, h21, h8, hlam]
                      · rcases h4bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          rcases p23_3 (m.d 0 4) (by simp) with h25 | h25
                          · rcases p23_3 (m.d 1 4) (by simp) with h26 | h26
                            · linarith only [h2, h26, hlam]
                            · rcases p23_3 (m.d 2 4) (by simp) with h28 | h28
                              · linarith only [h28, h4, hlam]
                              · rcases p23_3 (m.d 3 4) (by simp) with h30 | h30
                                · linarith only [h30, h6, hlam]
                                · rcases p23_3 (m.d 4 5) (by simp) with h32 | h32
                                  · linarith only [h32, h7, hlam]
                                  · linarith only [h12, h32, hlam]
                          · linarith only [h2, h25, hlam]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          rcases p23_3 (m.d 0 4) (by simp) with h36 | h36
                          · rcases p23_3 (m.d 1 4) (by simp) with h37 | h37
                            · linarith only [h2, h37, hlam]
                            · linarith only [h37, h8, hlam]
                          · linarith only [h36, h4, hlam]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          rcases p23_3 (m.d 0 4) (by simp) with h41 | h41
                          · rcases p23_3 (m.d 1 4) (by simp) with h42 | h42
                            · linarith only [h2, h42, hlam]
                            · linarith only [h10, h42, hlam]
                          · linarith only [h41, h6, hlam]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, h12, h3, h6, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1, u1elo0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h2, hlam, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h12, h18, hc34, hc45, hlam, hphi, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1, u1elo0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h12, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h4, hlam, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h8, hlam, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1, u1elo0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h19, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h6, hlam, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h10, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h18, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h21, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h7, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, h3, h6, h7, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1, u1elo0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, h18, h3, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1, u1elo0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, h3, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1, u1elo0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                  · linarith only [h1, h10, h18, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                · linarith only [h10, h11, h68, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                    · linarith only [h68, h71, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h73 | h73
                      · linarith only [h10, h11, h68, h73, hlam]
                      · linarith only [h0, h10, h11, h3, h6, h7, h73, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h10, h11, h70, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
              · linarith only [h0, h10, h3, h6, h77, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                  · linarith only [h0, h10, h3, h80, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h82 | h82
                    · linarith only [h0, h8, h82, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h2, h79, h82, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                  · linarith only [h0, h10, h3, h85, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                    · linarith only [h0, h4, h79, h87, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                      · linarith only [h0, h3, h6, h79, h8, h85, h89, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h0, h10, h3, h6, h7, h89, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · linarith only [h0, h5, h8, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
          · linarith only [h0, h4, h8, h93, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
            · rcases m.htr 1 3 5 (by decide) (by decide) with h96 | h96
              · rcases m.htr 1 4 5 (by decide) (by decide) with h97 | h97
                · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
                      · linarith only [h0, h100, h3, h98, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h100, h2, h97, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h8, h97, h99, hlam]
                  · linarith only [h1, h95, h98, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                    · linarith only [h0, h105, h106, h3, h8, h97, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h0, h106, h3, h6, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1, h105, h95, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                · linarith only [h110, h95, h96, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h113 | h113
                    · linarith only [h0, h110, h112, h113, h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h0, h113, h3, h6, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h112, h95, h96, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h117 | h117
              · linarith only [h0, h117, h3, h6, h95, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                  · linarith only [h0, h120, h3, h95, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h122 | h122
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                      · rcases h4bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [hlam, p124_0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h0, h119, h3, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h0, h122, h3, h6, h93, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p124_1, u1elo0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h0, h120, h122, h3, h6, h93, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p124_1, u1elo0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          rcases p124_3 (m.d 0 4) (by simp) with h129 | h129
                          · rcases p124_3 (m.d 1 4) (by simp) with h130 | h130
                            · linarith only [h130, h2, hlam]
                            · linarith only [h119, h130, hlam]
                          · linarith only [h129, hlam, p124_0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h2, hlam, p124_1]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [hlam, p124_0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h8, hlam, p124_0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h95, hlam, p124_1]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h4, hlam, p124_1]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h0, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p124_1, u1elo0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [hlam, p124_0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h120, hlam, p124_1]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h0, h120, h3, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h6, hlam, p124_1]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h0, h119, h3, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h0, h3, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p124_1, u1elo0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [hlam, p124_0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h0, h3, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h7, hlam, p124_0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h119, hlam, p124_0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h122, hlam, p124_0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [h123, hlam, p124_0]
                        · have p124_0 := h124c.1
                          have p124_1 := h124c.2.1
                          have p124_2 := h124c.2.2.1
                          have p124_3 := h124c.2.2.2
                          linarith only [hlam, p124_0]
                      · linarith only [h119, h120, h123, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h122, h3, h6, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                  · linarith only [h0, h156, h3, h95, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h158 | h158
                    · linarith only [h0, h119, h158, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h0, h158, h3, h6, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h161 | h161
        · rcases m.htr 1 2 5 (by decide) (by decide) with h162 | h162
          · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
            · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
              · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
                · linarith only [h165, h7, hlam, hphi, ht01, u0ehi8, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h168 | h168
                    · linarith only [h161, h168, h7, hlam, hphi, ht01, u0ehi8, u1elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h170 | h170
                      · linarith only [h0, h162, h167, h168, h170, h7, hlam, hphi, ht01, u0ehi8, u1elo0]
                      · rcases h4bigk with h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h7, hc14, hc45, hlam, hphi, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h7, hc24, hc45, hlam, hphi, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h7, hc34, hc45, hlam, hphi, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h7, hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h2, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h167, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p172_1, u1elo0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h0, h161, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p172_1, u1elo0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h165, hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h4, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h161, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h0, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p172_1, u1elo0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h168, hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h6, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h163, hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h167, hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h170, hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p172_1, u0ehi8]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          rcases p172_3 (m.d 0 4) (by simp) with h194 | h194
                          · linarith only [h194, h7, hlam]
                          · linarith only [h194, h2, hlam]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          rcases p172_3 (m.d 0 4) (by simp) with h197 | h197
                          · linarith only [h197, h7, hlam]
                          · linarith only [h197, h4, hlam]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          rcases p172_3 (m.d 0 4) (by simp) with h200 | h200
                          · linarith only [h200, h7, hlam]
                          · linarith only [h200, h6, hlam]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hlam, p172_0]
                  · linarith only [h1, h163, h167, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                · linarith only [h205, h7, hlam, hphi, ht01, u0ehi8, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h208 | h208
                    · linarith only [h0, h161, h208, h7, hlam, hphi, ht01, u0ehi8, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                      · linarith only [h0, h162, h163, h164, h210, h7, hlam, hphi, ht01, u0ehi8, u1elo0]
                      · rcases h4bigk with h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [hlam, p212_0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h7, hc14, hc45, hlam, hphi, p212_1]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h7, hc24, hc45, hlam, hphi, p212_1]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h7, hc34, hc45, hlam, hphi, p212_1]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h7, hlam, p212_0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h2, hlam, p212_1]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [hlam, p212_0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p212_1, u1elo0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h0, h162, h163, h164, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p212_1, u1elo0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h205, hlam, p212_0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h4, hlam, p212_1]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h161, hlam, p212_1]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [hlam, p212_0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h0, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p212_1, u1elo0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h208, hlam, p212_0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h6, hlam, p212_1]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h163, hlam, p212_0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h207, hlam, p212_0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [hlam, p212_0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [h210, hlam, p212_0]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p212_1, u0ehi8]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          rcases p212_3 (m.d 0 4) (by simp) with h234 | h234
                          · linarith only [h234, h7, hlam]
                          · linarith only [h2, h234, hlam]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          rcases p212_3 (m.d 0 4) (by simp) with h237 | h237
                          · linarith only [h237, h7, hlam]
                          · linarith only [h237, h4, hlam]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          rcases p212_3 (m.d 0 4) (by simp) with h240 | h240
                          · linarith only [h240, h7, hlam]
                          · linarith only [h240, h6, hlam]
                        · have p212_0 := h212c.1
                          have p212_1 := h212c.2.1
                          have p212_2 := h212c.2.2.1
                          have p212_3 := h212c.2.2.2
                          linarith only [hlam, p212_0]
                  · linarith only [h0, h162, h163, h164, h207, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h245 | h245
              · linarith only [h0, h163, h245, h3, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h247 | h247
                · linarith only [h247, h7, hlam, hphi, ht01, u0ehi8, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
                  · linarith only [h0, h163, h249, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h251 | h251
                    · linarith only [h251, h7, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h253 | h253
                      · linarith only [h253, h7, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                      · rcases h4bigk with h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [hlam, p255_0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h7, hc14, hc45, hlam, hphi, p255_1]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h7, hc24, hc45, hlam, hphi, p255_1]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h163, h7, hc13, hc45, hlam, hphi, ht34, p255_1]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h7, hlam, p255_0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h2, hlam, p255_1]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [hlam, p255_0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p255_1, u1elo0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h163, hlam, p255_1]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h247, hlam, p255_0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h4, hlam, p255_1]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h161, hlam, p255_1]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [hlam, p255_0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h249, hlam, p255_1]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h251, hlam, p255_0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h6, hlam, p255_1]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h0, h3, h6, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p255_1, u1elo0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h0, h3, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p255_1, u1elo0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [hlam, p255_0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h253, hlam, p255_0]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p255_1, u0ehi8]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          rcases p255_3 (m.d 0 4) (by simp) with h277 | h277
                          · linarith only [h277, h7, hlam]
                          · linarith only [h2, h277, hlam]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          rcases p255_3 (m.d 0 4) (by simp) with h280 | h280
                          · linarith only [h280, h7, hlam]
                          · linarith only [h280, h4, hlam]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [h249, hc23, hc45, hlam, hphi, ht34, p255_1]
                        · have p255_0 := h255c.1
                          have p255_1 := h255c.2.1
                          have p255_2 := h255c.2.2.1
                          have p255_3 := h255c.2.2.2
                          linarith only [hlam, p255_0]
          · linarith only [h0, h161, h162, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
          · linarith only [h0, h161, h286, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
            · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
              · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                · linarith only [h290, h7, hlam, hphi, ht01, u0ehi8, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h292 | h292
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                    · linarith only [h0, h292, h293, h3, h7, hlam, hphi, ht01, u0ehi8, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h295 | h295
                      · linarith only [h0, h161, h292, h295, h3, h7, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi8, u1elo0]
                      · rcases h4bigk with h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h7, hc14, hc45, hlam, hphi, p297_1]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h161, h7, hc12, hc45, hlam, hphi, ht23, ht34, p297_1]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h7, hc34, hc45, hlam, hphi, p297_1]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h7, hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h2, hlam, p297_1]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h161, hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p297_1, u1elo0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h290, hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h4, hlam, p297_1]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h0, h292, h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p297_1, u1elo0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h0, h292, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p297_1, u1elo0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h293, hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h6, hlam, p297_1]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h288, hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h292, hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h295, hlam, p297_0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h0, h161, h292, h3, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p297_1, u0ehi8, u1elo0]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          rcases p297_3 (m.d 0 4) (by simp) with h319 | h319
                          · linarith only [h319, h7, hlam]
                          · linarith only [h2, h319, hlam]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [h161, hc12, hc45, hlam, hphi, ht23, ht34, p297_1]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          rcases p297_3 (m.d 0 4) (by simp) with h323 | h323
                          · linarith only [h323, h7, hlam]
                          · linarith only [h323, h6, hlam]
                        · have p297_0 := h297c.1
                          have p297_1 := h297c.2.1
                          have p297_2 := h297c.2.2.1
                          have p297_3 := h297c.2.2.2
                          linarith only [hlam, p297_0]
                  · linarith only [h1, h288, h292, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h328 | h328
                · linarith only [h328, h7, hlam, hphi, ht01, u0ehi8, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h331 | h331
                    · linarith only [h0, h3, h330, h331, h7, hlam, hphi, ht01, u0ehi8, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h333 | h333
                      · linarith only [h288, h333, h7, hlam, hphi, ht01, u0ehi8, u1elo2]
                      · rcases h4bigk with h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h7, hc14, hc45, hlam, hphi, p335_1]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h161, h7, hc12, hc45, hlam, hphi, ht23, ht34, p335_1]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h7, hc34, hc45, hlam, hphi, p335_1]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h7, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h2, hlam, p335_1]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h161, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p335_1, u1elo0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h328, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h4, hlam, p335_1]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h0, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p335_1, u1elo0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h0, h3, h330, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p335_1, u1elo0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h331, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h6, hlam, p335_1]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h288, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h330, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h333, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p335_1, u0ehi8]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          rcases p335_3 (m.d 0 4) (by simp) with h357 | h357
                          · linarith only [h357, h7, hlam]
                          · linarith only [h2, h357, hlam]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h161, hc12, hc45, hlam, hphi, ht23, ht34, p335_1]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          rcases p335_3 (m.d 0 4) (by simp) with h361 | h361
                          · linarith only [h361, h7, hlam]
                          · linarith only [h361, h6, hlam]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hlam, p335_0]
                  · linarith only [h0, h286, h288, h289, h330, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h366 | h366
              · linarith only [h0, h288, h3, h366, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h368 | h368
                · linarith only [h368, h7, hlam, hphi, ht01, u0ehi8, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h370 | h370
                  · linarith only [h0, h288, h3, h370, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h372 | h372
                    · linarith only [h372, h7, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h374 | h374
                      · linarith only [h0, h3, h374, h6, h7, hlam, hphi, ht01, u0ehi8, u1elo0]
                      · rcases h4bigk with h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [hlam, p376_0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h7, hc14, hc45, hlam, hphi, p376_1]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h161, h7, hc12, hc45, hlam, hphi, ht23, ht34, p376_1]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h161, h370, h7, hc12, hc45, hlam, hphi, ht23, ht34, p376_1]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h7, hlam, p376_0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h2, hlam, p376_1]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [hlam, p376_0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h161, hlam, p376_0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h288, hlam, p376_1]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h368, hlam, p376_0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h4, hlam, p376_1]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h0, h3, h370, h6, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p376_1, u1elo0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [hlam, p376_0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h370, hlam, p376_1]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h372, hlam, p376_0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h6, hlam, p376_1]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h0, h161, h3, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p376_1, u1elo0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h0, h3, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p376_1, u1elo0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [hlam, p376_0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h374, hlam, p376_0]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p376_1, u0ehi8]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          rcases p376_3 (m.d 0 4) (by simp) with h398 | h398
                          · linarith only [h398, h7, hlam]
                          · linarith only [h2, h398, hlam]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h161, hc12, hc45, hlam, hphi, ht23, ht34, p376_1]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [h161, h370, hc12, hc45, hlam, hphi, ht23, ht34, p376_1]
                        · have p376_0 := h376c.1
                          have p376_1 := h376c.2.1
                          have p376_2 := h376c.2.2.1
                          have p376_3 := h376c.2.2.2
                          linarith only [hlam, p376_0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
      · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
        · rcases m.htr 1 2 5 (by decide) (by decide) with h406 | h406
          · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
            · linarith only [h407, h6, hlam, hphi, ht01, u0ehi7, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
              · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                  · linarith only [h411, h6, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h413 | h413
                    · linarith only [h0, h405, h413, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h2, h410, h413, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h4, h404, h407, h409, h410, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h417 | h417
                · rcases m.htr 2 3 4 (by decide) (by decide) with h418 | h418
                  · linarith only [h418, h6, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h420 | h420
                    · linarith only [h0, h405, h420, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h2, h417, h420, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h423 | h423
                  · linarith only [h423, h6, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h425 | h425
                    · linarith only [h0, h4, h407, h417, h425, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h427 | h427
                      · rcases h4bigk with h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          rcases p428_3 (m.d 0 4) (by simp) with h430 | h430
                          · rcases p428_3 (m.d 1 4) (by simp) with h431 | h431
                            · linarith only [h2, h431, hlam]
                            · rcases p428_3 (m.d 2 4) (by simp) with h433 | h433
                              · linarith only [h4, h433, hlam]
                              · rcases p428_3 (m.d 3 4) (by simp) with h435 | h435
                                · rcases p428_3 (m.d 4 5) (by simp) with h436 | h436
                                  · linarith only [h404, h436, hlam]
                                  · linarith only [h417, h436, hlam]
                                · linarith only [h407, h435, hlam]
                          · linarith only [h2, h430, hlam]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          rcases p428_3 (m.d 0 4) (by simp) with h441 | h441
                          · rcases p428_3 (m.d 1 4) (by simp) with h442 | h442
                            · linarith only [h2, h442, hlam]
                            · linarith only [h405, h442, hlam]
                          · linarith only [h4, h441, hlam]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h6, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h0, h4, h405, h417, h423, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p428_1, u1elo0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h2, hlam, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h417, h423, h427, hc23, hc35, hlam, hphi, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h407, hlam, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h417, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h4, hlam, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h405, hlam, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h423, hlam, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h425, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p428_1, u0ehi8]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          rcases p428_3 (m.d 0 4) (by simp) with h459 | h459
                          · linarith only [h459, h6, hlam]
                          · linarith only [h2, h459, hlam]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          rcases p428_3 (m.d 0 4) (by simp) with h462 | h462
                          · linarith only [h462, h6, hlam]
                          · linarith only [h4, h462, hlam]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h405, h417, h423, hc23, hc34, hlam, hphi, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h404, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h0, h4, h404, h405, h423, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p428_1, u1elo0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h0, h4, h404, h423, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p428_1, u1elo0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h427, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                      · linarith only [h0, h4, h404, h427, h6, hlam, hphi, ht01, u0ehi7, u1elo0]
          · linarith only [h0, h405, h406, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h474 | h474
          · linarith only [h0, h4, h405, h474, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h476 | h476
            · linarith only [h476, h6, hlam, hphi, ht01, u0ehi7, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h478 | h478
              · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
                · rcases m.htr 2 3 4 (by decide) (by decide) with h480 | h480
                  · linarith only [h0, h4, h405, h480, h6, hc12, hc23, hlam, hphi, ht01, u0ehi7, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h482 | h482
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h483 | h483
                      · rcases h4bigk with h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h0, h4, h476, h478, h483, hc45, hlam, hphi, ht01, ht0b, ht5b, p484_1, u1elo0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h0, h4, h474, h482, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p484_1, u1elo0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h6, hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          rcases p484_3 (m.d 0 4) (by simp) with h489 | h489
                          · rcases p484_3 (m.d 1 4) (by simp) with h490 | h490
                            · linarith only [h2, h490, hlam]
                            · linarith only [h479, h490, hlam]
                          · linarith only [h489, hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h2, hlam, p484_1]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h405, hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h476, hlam, p484_1]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p484_1, u1elo0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h4, hlam, p484_1]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h0, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p484_1, u1elo0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h480, hlam, p484_1]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h0, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p484_1, u1elo0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p484_1, u0ehi8]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          rcases p484_3 (m.d 0 4) (by simp) with h505 | h505
                          · linarith only [h505, h6, hlam]
                          · linarith only [h2, h505, hlam]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h474, h482, hc12, hc34, hlam, hphi, ht23, p484_1]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          rcases p484_3 (m.d 0 4) (by simp) with h510 | h510
                          · linarith only [h510, h6, hlam]
                          · linarith only [h404, h510, hlam]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h404, hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h479, hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h482, hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [h483, hlam, p484_0]
                        · have p484_0 := h484c.1
                          have p484_1 := h484c.2.1
                          have p484_2 := h484c.2.2.1
                          have p484_3 := h484c.2.2.2
                          linarith only [hlam, p484_0]
                      · linarith only [h0, h4, h474, h482, h483, h6, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi7, u1elo0]
                    · linarith only [h2, h479, h480, h482, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h0, h4, h404, h476, h478, h479, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                · rcases m.htr 2 3 4 (by decide) (by decide) with h522 | h522
                  · linarith only [h522, h6, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h524 | h524
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h525 | h525
                      · rcases h4bigk with h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h0, h4, h521, hc45, hlam, hphi, ht01, ht0b, ht5b, p526_1, u1elo0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h0, h4, h474, h524, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p526_1, u1elo0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h6, hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          rcases p526_3 (m.d 0 4) (by simp) with h531 | h531
                          · rcases p526_3 (m.d 1 4) (by simp) with h532 | h532
                            · linarith only [h2, h532, hlam]
                            · linarith only [h521, h532, hlam]
                          · linarith only [h531, hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h2, hlam, p526_1]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h405, hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h476, hlam, p526_1]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p526_1, u1elo0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h4, hlam, p526_1]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h0, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p526_1, u1elo0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h522, hlam, p526_1]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h0, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p526_1, u1elo0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p526_1, u0ehi8]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          rcases p526_3 (m.d 0 4) (by simp) with h547 | h547
                          · linarith only [h547, h6, hlam]
                          · linarith only [h2, h547, hlam]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h474, h524, hc12, hc34, hlam, hphi, ht23, p526_1]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          rcases p526_3 (m.d 0 4) (by simp) with h552 | h552
                          · linarith only [h552, h6, hlam]
                          · linarith only [h404, h552, hlam]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h404, hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h521, hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h524, hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [h525, hlam, p526_0]
                        · have p526_0 := h526c.1
                          have p526_1 := h526c.2.1
                          have p526_2 := h526c.2.2.1
                          have p526_3 := h526c.2.2.2
                          linarith only [hlam, p526_0]
                      · linarith only [h2, h521, h525, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h405, h521, h524, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h562 | h562
                  · linarith only [h0, h4, h404, h405, h521, h562, h6, hc12, hc23, hlam, hphi, ht01, u0ehi7, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h564 | h564
                    · linarith only [h0, h4, h405, h521, h564, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h0, h4, h404, h405, h564, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h567 | h567
        · rcases m.htr 1 2 5 (by decide) (by decide) with h568 | h568
          · rcases m.htr 1 3 4 (by decide) (by decide) with h569 | h569
            · linarith only [h569, h6, hlam, hphi, ht01, u0ehi7, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h571 | h571
              · rcases m.htr 1 4 5 (by decide) (by decide) with h572 | h572
                · linarith only [h404, h567, h572, hlam, hphi, ht01, u0ehi8, u1elo1]
                · linarith only [h569, h571, h572, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h575 | h575
                · linarith only [h404, h575, h6, hlam, hphi, ht01, u0ehi7, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h577 | h577
                  · linarith only [h577, h6, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h579 | h579
                    · linarith only [h404, h579, h6, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h581 | h581
                      · linarith only [h404, h581, h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                      · linarith only [h0, h568, h577, h579, h581, h6, hc23, hc45, hlam, hphi, ht01, ht34, u0ehi7, u1elo0]
          · linarith only [h0, h5, h567, h568, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h585 | h585
          · linarith only [h0, h4, h567, h585, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h587 | h587
            · linarith only [h587, h6, hlam, hphi, ht01, u0ehi7, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h589 | h589
              · rcases m.htr 1 4 5 (by decide) (by decide) with h590 | h590
                · linarith only [h404, h590, h6, hlam, hphi, ht01, u0ehi7, u1elo3]
                · linarith only [h587, h589, h590, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h593 | h593
                · linarith only [h0, h4, h404, h567, h593, h6, hlam, hphi, ht01, u0ehi7, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                  · linarith only [h0, h4, h567, h595, h6, hc12, hc23, hlam, hphi, ht01, u0ehi7, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h597 | h597
                    · linarith only [h0, h4, h404, h597, h6, hlam, hphi, ht01, u0ehi7, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h599 | h599
                      · linarith only [h0, h404, h5, h567, h597, h599, h6, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi7, u1elo0]
                      · linarith only [h0, h5, h567, h597, h599, h6, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi7, u1elo0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h602 | h602
    · rcases m.htr 0 4 5 (by decide) (by decide) with h603 | h603
      · linarith only [h3, h5, h602, h603, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h605 | h605
        · rcases m.htr 1 2 5 (by decide) (by decide) with h606 | h606
          · linarith only [h0, h3, h5, h602, h606, hlam, hphi, ht01, u0ehi8, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h608 | h608
            · rcases m.htr 1 3 5 (by decide) (by decide) with h609 | h609
              · rcases m.htr 1 4 5 (by decide) (by decide) with h610 | h610
                · linarith only [h603, h610, hlam, hphi, ht01, u0ehi8, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h612 | h612
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h613 | h613
                    · linarith only [h1, h603, h605, h606, h609, h613, hlam, hphi, ht01, u0ehi8, u1elo0]
                    · linarith only [h3, h5, h612, h613, hc34, hc45, hlam, hphi]
                  · linarith only [h1, h608, h612, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h617 | h617
                · linarith only [h603, h605, h617, hlam, hphi, ht01, u0ehi8, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h619 | h619
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h620 | h620
                    · linarith only [h0, h603, h605, h620, hlam, hphi, ht01, u0ehi8, u1elo0]
                    · linarith only [h3, h5, h619, h620, hc34, hc45, hlam, hphi]
                  · linarith only [h1, h608, h619, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h624 | h624
              · linarith only [h3, h5, h602, h608, h624, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h626 | h626
                · linarith only [h3, h5, h602, h603, h608, h626, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h628 | h628
                  · linarith only [h3, h5, h608, h628, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h630 | h630
                    · linarith only [h0, h603, h605, h630, hlam, hphi, ht01, u0ehi8, u1elo0]
                    · linarith only [h3, h5, h602, h608, h630, hc13, hc45, hlam, hphi, ht34]
        · linarith only [h4, h5, h605, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h634 | h634
      · linarith only [h4, h5, h634, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
        · rcases m.htr 1 2 5 (by decide) (by decide) with h637 | h637
          · linarith only [h0, h5, h637, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h639 | h639
            · linarith only [h602, h639, hlam, hphi, ht01, u0ehi7, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h641 | h641
              · linarith only [h636, h637, h639, h641, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h643 | h643
                · linarith only [h602, h634, h636, h643, hlam, hphi, ht01, u0ehi7, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h645 | h645
                  · linarith only [h602, h645, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h647 | h647
                    · linarith only [h0, h602, h634, h636, h647, hlam, hphi, ht01, u0ehi7, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h649 | h649
                      · linarith only [h4, h5, h602, h647, h649, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                      · linarith only [h602, h649, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
        · linarith only [h4, h5, h636, hc12, hc25, hlam, hphi]

end R2N4
