import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h10, h15, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h13, h15, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h13, h14, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                    · linarith only [h0, h13, h19, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h13, h21, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                        · linarith only [h0, h10, h13, h19, h23, h4, h7, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                          · linarith only [h0, h11, h25, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                            · linarith only [h0, h21, h25, h27, h4, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h13, h27, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
              · linarith only [h0, h10, h32, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                · linarith only [h0, h10, h34, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                            · linarith only [h1, h36, h41, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h0, h38, h4, h40, h41, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h32, h4, h40, h7, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h10, h37, h39, hlam]
                      · linarith only [h0, h10, h37, h38, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h36, h37, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                    · linarith only [h0, h36, h4, h48, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                      · linarith only [h0, h36, h4, h50, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h4, h50, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
            · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
              · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                      · linarith only [h0, h53, h58, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h56, h58, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h56, h57, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h56, h7, h9, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h53, h55, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h5, h53, h54, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
              · linarith only [h0, h4, h53, h65, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h5, h65, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
        · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
          · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
              · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                · rcases m.htr 1 3 4 (by decide) (by decide) with h74 | h74
                  · linarith only [h1, h69, h7, h74, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                      · linarith only [h0, h1, h4, h7, h76, h77, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                        · linarith only [h0, h72, h77, h79, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1, h7, h76, h79, hc23, hc34, hlam, hphi]
                    · linarith only [h69, h7, h76, hc13, hc34, hlam, hphi]
                · linarith only [h72, h73, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h0, h5, h71, h72, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
              · linarith only [h0, h4, h71, h85, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                · linarith only [h0, h4, h71, h87, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                  · linarith only [h1, h7, h89, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                      · linarith only [h4, h7, h92, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                            · rcases h0bigk with h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [hlam, p97_0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h5, h92, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p97_1, u0elo0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h6, h69, h87, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p97_1, u0elo0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h6, h69, h7, h87, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p97_1, u0elo0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h6, h87, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p97_1, u0elo0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h0, hlam, p97_0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [hlam, p97_0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h6, h69, h87, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p97_1, u0elo1]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h0, h6, h69, h7, h87, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p97_1, u0elo0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h0, h6, h87, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p97_1, u0elo0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h1, hlam, p97_1]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h4, hlam, p97_1]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [hlam, p97_0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h7, hlam, p97_1]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h6, h87, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p97_1, u0elo2]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h2, hlam, p97_0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h5, hlam, p97_0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h1, h91, h96, hc45, hlam, hphi, ht0b, ht5b, p97_1, u0elo3]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [hlam, p97_0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h0, h5, h6, h87, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p97_1, u0elo0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h3, hlam, p97_0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h6, hlam, p97_1]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h69, hlam, p97_0]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [h70, hlam, p97_1]
                              · have p97_0 := h97c.1
                                have p97_1 := h97c.2.1
                                have p97_2 := h97c.2.2.1
                                have p97_3 := h97c.2.2.2
                                linarith only [hlam, p97_0]
                            · linarith only [h2, h7, h89, h91, h96, hc35, hlam, hphi, u5elo4]
                          · linarith only [h70, h87, h92, h94, h95, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h71, h91, h94, hlam]
                    · linarith only [h69, h7, h91, hc13, hc34, hlam, hphi]
          · linarith only [h69, h7, h70, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
          · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
            · rcases m.htr 1 2 4 (by decide) (by decide) with h130 | h130
              · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                  · linarith only [h1, h132, h69, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                    · linarith only [h1, h134, h69, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                      · linarith only [h1, h129, h136, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                        · linarith only [h1, h129, h138, h69, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
                          · linarith only [h0, h130, h140, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h142 | h142
                            · rcases h0bigk with h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h0, h131, hc25, hlam, hphi, ht0b, ht5b, p143_1, u0elo0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                rcases p143_3 (m.d 0 1) (by simp) with h146 | h146
                                · rcases p143_3 (m.d 0 2) (by simp) with h147 | h147
                                  · linarith only [h0, h147, hlam]
                                  · linarith only [h147, h4, hlam]
                                · linarith only [h1, h146, hlam]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h128, h136, h140, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1, u0elo0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h128, h136, h140, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1, u0elo0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h0, hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                rcases p143_3 (m.d 0 1) (by simp) with h155 | h155
                                · rcases p143_3 (m.d 0 2) (by simp) with h156 | h156
                                  · rcases p143_3 (m.d 0 3) (by simp) with h157 | h157
                                    · linarith only [h157, h4, hlam]
                                    · rcases p143_3 (m.d 0 4) (by simp) with h159 | h159
                                      · linarith only [h159, h5, hlam]
                                      · linarith only [h159, h7, hlam]
                                  · linarith only [h156, h4, hlam]
                                · linarith only [h1, h155, hlam]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h128, h136, h140, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1, u0elo1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h0, h128, h136, h140, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1, u0elo0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h1, hlam, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h4, hlam, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h7, hlam, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h69, hlam, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h2, hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h5, hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                rcases p143_3 (m.d 0 1) (by simp) with h173 | h173
                                · rcases p143_3 (m.d 0 2) (by simp) with h174 | h174
                                  · rcases p143_3 (m.d 0 3) (by simp) with h175 | h175
                                    · linarith only [h175, h7, hlam]
                                    · rcases p143_3 (m.d 0 4) (by simp) with h177 | h177
                                      · rcases p143_3 (m.d 0 5) (by simp) with h178 | h178
                                        · linarith only [h128, h178, hlam]
                                        · linarith only [h178, h69, hlam]
                                      · linarith only [h177, h7, hlam]
                                  · linarith only [h174, h4, hlam]
                                · linarith only [h1, h173, hlam]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h128, h136, h140, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1, u0elo3]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h3, hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h6, hlam, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h1, h129, hc23, hlam, hphi, ht34, ht45, p143_1, u5elo0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h128, hlam, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [hlam, p143_0]
                            · linarith only [h1, h129, h142, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h129, h131, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h129, h130, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h129, h4, h69, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
            · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
              · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                  · linarith only [h1, h198, h7, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h200 | h200
                    · linarith only [h1, h128, h200, h69, h7, hc05, hlam, hphi, u5elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                      · linarith only [h0, h195, h202, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                        · linarith only [h128, h195, h198, h2, h204, h69, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                          · linarith only [h128, h196, h2, h206, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                            · rcases h0bigk with h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u0elo0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 1) (by simp) with h212 | h212
                                · rcases p209_3 (m.d 0 2) (by simp) with h213 | h213
                                  · linarith only [h0, h213, hlam]
                                  · linarith only [h213, h4, hlam]
                                · linarith only [h1, h212, hlam]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 1) (by simp) with h217 | h217
                                · rcases p209_3 (m.d 0 2) (by simp) with h218 | h218
                                  · linarith only [h0, h218, hlam]
                                  · linarith only [h218, h5, hlam]
                                · linarith only [h2, h217, hlam]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 1) (by simp) with h222 | h222
                                · rcases p209_3 (m.d 0 2) (by simp) with h223 | h223
                                  · linarith only [h0, h223, hlam]
                                  · linarith only [h223, h6, hlam]
                                · linarith only [h222, h3, hlam]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h0, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 1) (by simp) with h229 | h229
                                · rcases p209_3 (m.d 0 2) (by simp) with h230 | h230
                                  · rcases p209_3 (m.d 0 3) (by simp) with h231 | h231
                                    · linarith only [h231, h4, hlam]
                                    · rcases p209_3 (m.d 0 4) (by simp) with h233 | h233
                                      · linarith only [h233, h5, hlam]
                                      · linarith only [h233, h7, hlam]
                                  · linarith only [h230, h4, hlam]
                                · linarith only [h1, h229, hlam]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 1) (by simp) with h238 | h238
                                · rcases p209_3 (m.d 0 2) (by simp) with h239 | h239
                                  · rcases p209_3 (m.d 0 3) (by simp) with h240 | h240
                                    · linarith only [h240, h4, hlam]
                                    · rcases p209_3 (m.d 0 4) (by simp) with h242 | h242
                                      · linarith only [h242, h5, hlam]
                                      · rcases p209_3 (m.d 0 5) (by simp) with h244 | h244
                                        · linarith only [h244, h6, hlam]
                                        · linarith only [h128, h244, hlam]
                                  · linarith only [h239, h5, hlam]
                                · linarith only [h2, h238, hlam]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 1) (by simp) with h249 | h249
                                · rcases p209_3 (m.d 0 2) (by simp) with h250 | h250
                                  · rcases p209_3 (m.d 0 3) (by simp) with h251 | h251
                                    · linarith only [h251, h4, hlam]
                                    · rcases p209_3 (m.d 0 4) (by simp) with h253 | h253
                                      · linarith only [h253, h5, hlam]
                                      · rcases p209_3 (m.d 0 5) (by simp) with h255 | h255
                                        · linarith only [h255, h6, hlam]
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
                                            linarith only [h0, h197, h202, h206, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1, u0elo0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            rcases p257_3 (m.d 0 2) (by simp) with h260 | h260
                                            · rcases p257_3 (m.d 1 2) (by simp) with h261 | h261
                                              · linarith only [h0, h261, hlam]
                                              · linarith only [h195, h261, hlam]
                                            · linarith only [h260, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            rcases p257_3 (m.d 0 2) (by simp) with h265 | h265
                                            · rcases p257_3 (m.d 1 2) (by simp) with h266 | h266
                                              · linarith only [h0, h266, hlam]
                                              · linarith only [h196, h266, hlam]
                                            · linarith only [h265, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            rcases p257_3 (m.d 0 2) (by simp) with h270 | h270
                                            · rcases p257_3 (m.d 1 2) (by simp) with h271 | h271
                                              · linarith only [h0, h271, hlam]
                                              · linarith only [h197, h271, hlam]
                                            · linarith only [h270, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h0, hlam, p257_0]
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
                                            linarith only [h0, h202, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1, u0elo0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h0, h202, h206, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1, u0elo0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h4, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h195, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h202, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h204, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h5, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h196, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h206, hc23, hlam, hphi, ht34, ht45, p257_1, u5elo2]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h206, hlam, p257_1]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h6, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h197, hlam, p257_0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h0, h197, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, p257_1, u0elo0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [h0, h197, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, p209_1, p257_1, u0elo0]
                                          · have p257_0 := h257c.1
                                            have p257_1 := h257c.2.1
                                            have p257_2 := h257c.2.2.1
                                            have p257_3 := h257c.2.2.2
                                            linarith only [hlam, p257_0]
                                  · linarith only [h250, h6, hlam]
                                · linarith only [h249, h3, hlam]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h1, hlam, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h4, hlam, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h7, hlam, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h69, hlam, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h2, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h5, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h1, h128, hc13, hlam, hphi, ht34, ht45, p209_1, u5elo0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h128, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h3, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h6, hlam, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h1, h69, hc13, hlam, hphi, ht34, ht45, p209_1, u5elo3]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h69, hc04, hlam, hphi, ht45, p209_1, u5elo3]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                            · linarith only [h1, h195, h208, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h195, h197, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h195, h196, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h195, h4, h69, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h317 | h317
    · rcases m.htr 0 3 4 (by decide) (by decide) with h318 | h318
      · linarith only [h318, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h320 | h320
        · rcases m.htr 0 4 5 (by decide) (by decide) with h321 | h321
          · rcases m.htr 1 2 3 (by decide) (by decide) with h322 | h322
            · rcases m.htr 1 2 4 (by decide) (by decide) with h323 | h323
              · linarith only [h0, h323, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h325 | h325
                · rcases m.htr 1 3 4 (by decide) (by decide) with h326 | h326
                  · linarith only [h1, h318, h326, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h328 | h328
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h329 | h329
                      · linarith only [h0, h1, h318, h322, h328, h329, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                        · linarith only [h2, h322, h323, h331, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1, h328, h331, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h318, h320, h328, hc13, hc34, hlam, hphi]
                · linarith only [h322, h325, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h322, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h321, h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h338 | h338
          · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
            · rcases m.htr 1 2 4 (by decide) (by decide) with h340 | h340
              · linarith only [h0, h340, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                · rcases m.htr 1 3 4 (by decide) (by decide) with h343 | h343
                  · linarith only [h1, h318, h343, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h345 | h345
                    · linarith only [h1, h320, h345, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h347 | h347
                      · linarith only [h2, h318, h339, h340, h347, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h349 | h349
                        · linarith only [h1, h320, h339, h349, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h351 | h351
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h352 | h352
                            · rcases h0bigk with h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [hlam, p353_0]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p353_1, u0elo0]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                rcases p353_3 (m.d 0 1) (by simp) with h356 | h356
                                · rcases p353_3 (m.d 0 2) (by simp) with h357 | h357
                                  · linarith only [h0, h357, hlam]
                                  · linarith only [h357, h4, hlam]
                                · linarith only [h1, h356, hlam]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h0, h342, h349, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p353_1, u0elo0]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                rcases p353_3 (m.d 0 1) (by simp) with h362 | h362
                                · rcases p353_3 (m.d 0 2) (by simp) with h363 | h363
                                  · linarith only [h0, h363, hlam]
                                  · linarith only [h317, h363, hlam]
                                · linarith only [h3, h362, hlam]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h0, hlam, p353_0]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [hlam, p353_0]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h1, h339, h347, h5, hc23, hc34, hlam, hphi, p353_1]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h5, hlam, p353_1]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h1, h320, h339, h347, h5, hc23, hc34, hlam, hphi, p353_1]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h1, hlam, p353_1]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h4, hlam, p353_1]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [hlam, p353_0]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h318, hlam, p353_1]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h320, hlam, p353_1]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h2, hlam, p353_0]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h0, h342, h349, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p353_1, u0elo3]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                rcases p353_3 (m.d 0 1) (by simp) with h379 | h379
                                · rcases p353_3 (m.d 0 2) (by simp) with h380 | h380
                                  · linarith only [h380, h5, hlam]
                                  · linarith only [h380, h4, hlam]
                                · linarith only [h1, h379, hlam]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [hlam, p353_0]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                rcases p353_3 (m.d 0 1) (by simp) with h385 | h385
                                · rcases p353_3 (m.d 0 2) (by simp) with h386 | h386
                                  · linarith only [h386, h5, hlam]
                                  · linarith only [h317, h386, hlam]
                                · linarith only [h3, h385, hlam]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h3, hlam, p353_0]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h317, hlam, p353_1]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h1, h339, hc23, hlam, hphi, ht34, ht45, p353_1, u5elo0]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [h338, hlam, p353_1]
                              · have p353_0 := h353c.1
                                have p353_1 := h353c.2.1
                                have p353_2 := h353c.2.2.1
                                have p353_3 := h353c.2.2.2
                                linarith only [hlam, p353_0]
                            · linarith only [h347, h352, h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h317, h338, h351, h5, hlam]
                · linarith only [h317, h342, h5, hc12, hc24, hlam, hphi]
            · linarith only [h339, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h317, h338, h5, hc25, hlam, hphi, u5elo4]
    · linarith only [h317, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]

end R2N4
