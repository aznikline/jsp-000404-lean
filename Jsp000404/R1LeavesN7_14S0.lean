import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
    · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
            · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
              · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                      · linarith only [h0, h10, h16, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h13, h16, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                      · linarith only [h0, h10, h19, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h13, h19, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h13, h14, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                  · linarith only [h0, h13, h23, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                      · linarith only [h0, h13, h26, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h0, h10, h23, h28, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                          · linarith only [h0, h11, h30, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h2, h25, h30, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                      · linarith only [h0, h10, h13, h25, h33, h4, h7, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                        · linarith only [h0, h23, h35, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                          · linarith only [h11, h25, h37, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                            · linarith only [h0, h25, h39, h4, h7, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h10, h13, h39, h4, h7, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
            · linarith only [h0, h10, h4, h44, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
              · linarith only [h0, h10, h4, h46, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                            · linarith only [h1, h48, h54, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h2, h50, h54, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h44, h50, h53, hlam]
                        · linarith only [h3, h44, h49, h50, h51, h52, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h10, h4, h51, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                          · linarith only [h0, h4, h50, h60, h62, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h4, h44, h62, h7, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h10, h49, h61, hlam]
                      · linarith only [h10, h48, h60, hlam]
                  · linarith only [h0, h4, h48, h49, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                  · linarith only [h0, h4, h48, h68, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h4, h48, h71, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h4, h7, h71, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                      · linarith only [h0, h10, h4, h48, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h4, h7, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
          · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
            · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
              · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                    · linarith only [h2, h82, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                      · linarith only [h0, h77, h84, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h80, h84, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h4, h8, h80, h81, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                  · linarith only [h0, h4, h7, h80, h88, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                    · linarith only [h2, h9, h90, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                      · linarith only [h0, h4, h80, h92, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                        · linarith only [h0, h4, h7, h77, h80, h88, h94, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                          · linarith only [h0, h5, h7, h77, h80, h9, h96, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                            · linarith only [h7, h9, h98, hlam]
                            · rcases h0bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h77, h8, h80, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h7, h77, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h77, h8, h80, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h0, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h77, h8, h80, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h0, h7, h77, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h0, h77, h8, h80, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h1, hlam, p100_1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h4, hlam, p100_1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h7, h77, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo2]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h0, h4, h77, h8, h80, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h2, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h5, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h7, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h9, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h3, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h6, hlam, p100_1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h8, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h7, h77, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo4]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
              · linarith only [h0, h6, h77, h79, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h5, h77, h78, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
            · linarith only [h0, h128, h4, h77, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
              · linarith only [h0, h130, h4, h77, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h134 | h134
                    · linarith only [h134, h2, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h137 | h137
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h138 | h138
                          · linarith only [h0, h130, h138, h5, h6, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h140 | h140
                            · linarith only [h1, h132, h140, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases h0bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h4, h77, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u0elo0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p142_1, u0elo0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h128, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h128, h5, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h0, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p142_1, u0elo1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h0, h128, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h0, h128, h5, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h1, hlam, p142_1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h4, hlam, p142_1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h128, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo2]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h0, h128, h4, h5, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h2, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h5, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h7, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h9, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h3, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h6, hlam, p142_1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h8, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h128, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo4]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hlam, p142_0]
                        · linarith only [h1, h128, h133, h136, h137, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h136, h4, h7, h77, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h132, h133, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                  · linarith only [h0, h132, h171, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h173, h2, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                      · linarith only [h132, h175, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h175, h4, h7, h77, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
        · linarith only [h178, h7, h8, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
          · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
            · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
              · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
                · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                  · linarith only [h1, h184, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h186 | h186
                    · linarith only [h178, h183, h184, h186, h2, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
                      · linarith only [h0, h180, h188, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h183, h188, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h183, h7, h8, hc13, hc35, hlam, hphi]
              · linarith only [h0, h180, h182, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h180, h181, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
            · linarith only [h0, h180, h194, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
              · linarith only [h0, h180, h196, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                  · linarith only [h1, h199, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h178, h2, h201, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                        · linarith only [h194, h204, h4, h5, h7, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                          · linarith only [h178, h206, h5, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                            · linarith only [h178, h194, h198, h208, h5, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases h0bigk with h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h180, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p210_1, u0elo0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h194, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h194, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h194, h5, h7, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h0, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h194, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h0, h194, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h0, h194, h5, h7, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h1, hlam, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h4, hlam, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h194, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo2]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h8, hlam, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h2, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h5, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h7, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h178, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h3, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h6, hlam, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h1, h198, hc34, hlam, hphi, ht0b, ht45, ht5b, p210_1, u0elo4]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h194, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo4]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [hlam, p210_0]
                      · linarith only [h1, h180, h198, h203, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h198, h7, h8, hc13, hc35, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h238 | h238
      · rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
        · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
          · rcases m.htr 1 2 4 (by decide) (by decide) with h241 | h241
            · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
              · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
                · linarith only [h1, h243, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h245 | h245
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                      · linarith only [h0, h240, h247, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h249 | h249
                        · linarith only [h0, h240, h249, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1, h245, h249, h7, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h239, h243, h245, h246, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h238, h245, h7, hc13, hc34, hlam, hphi]
              · linarith only [h0, h240, h242, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h240, h241, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
            · linarith only [h0, h240, h256, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
              · linarith only [h0, h240, h258, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                · linarith only [h1, h260, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h263 | h263
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h264 | h264
                      · linarith only [h0, h264, h4, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h266 | h266
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h267 | h267
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h268 | h268
                            · rcases h0bigk with h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [hlam, p269_0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h2, h260, h262, h268, h5, hc45, hlam, hphi, ht0b, ht5b, p269_1, u0elo0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h238, h258, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h2, h260, h262, h268, hc45, hlam, hphi, ht0b, ht5b, p269_1, u0elo0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h258, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h0, hlam, p269_0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [hlam, p269_0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h238, h258, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo1]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h0, h2, h260, h262, h268, hc45, hlam, hphi, ht0b, ht5b, p269_1, u0elo0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h0, h258, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h1, hlam, p269_1]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h4, hlam, p269_1]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [hlam, p269_0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h7, hlam, p269_1]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h258, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo2]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h2, hlam, p269_0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h5, hlam, p269_0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h0, h1, h262, h268, h5, hc45, hlam, hphi, ht0b, ht5b, p269_1, u0elo0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [hlam, p269_0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h0, h258, h5, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h3, hlam, p269_0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h6, hlam, p269_1]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h238, hlam, p269_0]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [h239, hlam, p269_1]
                              · have p269_0 := h269c.1
                                have p269_1 := h269c.2.1
                                have p269_2 := h269c.2.2.1
                                have p269_3 := h269c.2.2.2
                                linarith only [hlam, p269_0]
                            · linarith only [h238, h258, h268, h6, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h238, h256, h263, h267, h3, h7, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h256, h260, h262, h266, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h239, h260, h262, h263, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h238, h262, h7, hc13, hc34, hlam, hphi]
        · linarith only [h238, h239, h7, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h301 | h301
        · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
          · rcases m.htr 1 2 4 (by decide) (by decide) with h303 | h303
            · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
              · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
                · linarith only [h1, h305, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                  · linarith only [h1, h238, h307, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                      · linarith only [h0, h310, h4, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                        · linarith only [h1, h238, h302, h312, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h314 | h314
                          · linarith only [h0, h303, h314, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h2, h309, h314, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
                      · linarith only [h301, h302, h305, h309, h317, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h319 | h319
                        · linarith only [h238, h301, h302, h305, h309, h319, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h321 | h321
                          · linarith only [h0, h302, h305, h309, h321, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h323 | h323
                            · rcases h0bigk with h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                rcases p324_3 (m.d 0 1) (by simp) with h327 | h327
                                · rcases p324_3 (m.d 0 2) (by simp) with h328 | h328
                                  · linarith only [h0, h328, hlam]
                                  · linarith only [h328, h4, hlam]
                                · linarith only [h1, h327, hlam]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h301, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h301, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h0, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                rcases p324_3 (m.d 0 1) (by simp) with h336 | h336
                                · rcases p324_3 (m.d 0 2) (by simp) with h337 | h337
                                  · rcases p324_3 (m.d 0 3) (by simp) with h338 | h338
                                    · linarith only [h338, h4, hlam]
                                    · rcases p324_3 (m.d 0 4) (by simp) with h340 | h340
                                      · linarith only [h340, h5, hlam]
                                      · linarith only [h340, h7, hlam]
                                  · linarith only [h337, h4, hlam]
                                · linarith only [h1, h336, hlam]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h301, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h0, h301, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h1, hlam, p324_1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h4, hlam, p324_1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h7, hlam, p324_1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h238, hlam, p324_1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h2, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h5, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                rcases p324_3 (m.d 0 1) (by simp) with h354 | h354
                                · rcases p324_3 (m.d 0 2) (by simp) with h355 | h355
                                  · rcases p324_3 (m.d 0 3) (by simp) with h356 | h356
                                    · linarith only [h356, h7, hlam]
                                    · rcases p324_3 (m.d 0 4) (by simp) with h358 | h358
                                      · rcases p324_3 (m.d 0 5) (by simp) with h359 | h359
                                        · linarith only [h301, h359, hlam]
                                        · linarith only [h238, h359, hlam]
                                      · linarith only [h358, h7, hlam]
                                  · linarith only [h355, h4, hlam]
                                · linarith only [h1, h354, hlam]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h301, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo3]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h3, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h6, hlam, p324_1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                rcases p324_3 (m.d 0 1) (by simp) with h369 | h369
                                · rcases p324_3 (m.d 0 2) (by simp) with h370 | h370
                                  · rcases p324_3 (m.d 0 3) (by simp) with h371 | h371
                                    · linarith only [h238, h371, hlam]
                                    · rcases p324_3 (m.d 0 4) (by simp) with h373 | h373
                                      · rcases p324_3 (m.d 0 5) (by simp) with h374 | h374
                                        · rcases h2bigk with h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h0, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p375_1, u0elo0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            rcases p375_3 (m.d 0 2) (by simp) with h378 | h378
                                            · rcases p375_3 (m.d 1 2) (by simp) with h379 | h379
                                              · linarith only [h0, h379, hlam]
                                              · linarith only [h302, h379, hlam]
                                            · linarith only [h378, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            rcases p375_3 (m.d 0 2) (by simp) with h383 | h383
                                            · rcases p375_3 (m.d 1 2) (by simp) with h384 | h384
                                              · linarith only [h0, h384, hlam]
                                              · linarith only [h303, h384, hlam]
                                            · linarith only [h383, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            rcases p375_3 (m.d 0 2) (by simp) with h388 | h388
                                            · rcases p375_3 (m.d 1 2) (by simp) with h389 | h389
                                              · linarith only [h0, h389, hlam]
                                              · linarith only [h304, h389, hlam]
                                            · linarith only [h388, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h0, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p375_1, u0elo0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h0, hc24, hlam, hphi, ht0b, ht45, ht5b, p375_1, u0elo0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h0, h321, hc24, hlam, hphi, ht0b, ht45, ht5b, p375_1, u0elo0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h4, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h302, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h317, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h319, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h5, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h303, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p375_1, u0elo0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h321, hlam, p375_1]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h6, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h304, hlam, p375_0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h3, h304, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p375_1, u0elo0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [h0, h304, hc24, hlam, hphi, ht0b, ht45, ht5b, p375_1, u0elo0]
                                          · have p375_0 := h375c.1
                                            have p375_1 := h375c.2.1
                                            have p375_2 := h375c.2.2.1
                                            have p375_3 := h375c.2.2.2
                                            linarith only [hlam, p375_0]
                                        · linarith only [h238, h374, hlam]
                                      · linarith only [h373, h7, hlam]
                                  · linarith only [h370, h4, hlam]
                                · linarith only [h1, h369, hlam]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h301, hlam, p324_1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hlam, p324_0]
                            · linarith only [h1, h301, h302, h323, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
              · linarith only [h0, h302, h304, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h302, h303, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h422 | h422
            · linarith only [h0, h302, h4, h422, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h424 | h424
              · linarith only [h0, h302, h4, h424, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h426 | h426
                · linarith only [h302, h4, h426, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h428 | h428
                  · linarith only [h1, h238, h428, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h430 | h430
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h431 | h431
                      · linarith only [h4, h431, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h433 | h433
                        · linarith only [h238, h4, h433, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h435 | h435
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h436 | h436
                            · rcases h0bigk with h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [hlam, p437_0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h302, h433, h435, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p437_1, u0elo0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h302, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p437_1, u0elo0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h2, h430, hc45, hlam, hphi, ht0b, ht5b, p437_1, u0elo0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h302, h433, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p437_1, u0elo0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h0, hlam, p437_0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [hlam, p437_0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h302, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p437_1, u0elo1]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h0, h302, h433, h435, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p437_1, u0elo0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h0, h302, h433, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p437_1, u0elo0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h1, hlam, p437_1]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h4, hlam, p437_1]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [hlam, p437_0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h7, hlam, p437_1]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h238, hlam, p437_1]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h2, hlam, p437_0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h5, hlam, p437_0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h302, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p437_1, u0elo3]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [hlam, p437_0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h0, h302, h433, h5, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p437_1, u0elo0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h3, hlam, p437_0]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h6, hlam, p437_1]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h302, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p437_1, u0elo4]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [h301, hlam, p437_1]
                              · have p437_0 := h437c.1
                                have p437_1 := h437c.2.1
                                have p437_2 := h437c.2.2.1
                                have p437_3 := h437c.2.2.2
                                linarith only [hlam, p437_0]
                            · linarith only [h302, h4, h436, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h2, h430, h435, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h465 | h465
                      · linarith only [h301, h302, h4, h426, h430, h465, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h467 | h467
                        · linarith only [h0, h238, h465, h467, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h469 | h469
                          · linarith only [h0, h302, h426, h430, h469, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h301, h422, h469, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h472 | h472
          · rcases m.htr 1 2 4 (by decide) (by decide) with h473 | h473
            · rcases m.htr 1 2 5 (by decide) (by decide) with h474 | h474
              · rcases m.htr 1 3 4 (by decide) (by decide) with h475 | h475
                · linarith only [h1, h475, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
                  · linarith only [h1, h238, h477, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
                    · linarith only [h2, h301, h479, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h481 | h481
                      · linarith only [h1, h472, h481, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h483 | h483
                        · linarith only [h1, h238, h472, h483, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h485 | h485
                          · linarith only [h0, h1, h301, h472, h485, h5, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h487 | h487
                            · rcases h0bigk with h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1, u0elo0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h491 | h491
                                · rcases p488_3 (m.d 0 2) (by simp) with h492 | h492
                                  · linarith only [h0, h492, hlam]
                                  · linarith only [h4, h492, hlam]
                                · linarith only [h1, h491, hlam]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h496 | h496
                                · rcases p488_3 (m.d 0 2) (by simp) with h497 | h497
                                  · linarith only [h0, h497, hlam]
                                  · linarith only [h497, h5, hlam]
                                · linarith only [h2, h496, hlam]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h501 | h501
                                · rcases p488_3 (m.d 0 2) (by simp) with h502 | h502
                                  · linarith only [h0, h502, hlam]
                                  · linarith only [h502, h6, hlam]
                                · linarith only [h3, h501, hlam]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h0, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h508 | h508
                                · rcases p488_3 (m.d 0 2) (by simp) with h509 | h509
                                  · rcases p488_3 (m.d 0 3) (by simp) with h510 | h510
                                    · linarith only [h4, h510, hlam]
                                    · rcases p488_3 (m.d 0 4) (by simp) with h512 | h512
                                      · linarith only [h5, h512, hlam]
                                      · linarith only [h512, h7, hlam]
                                  · linarith only [h4, h509, hlam]
                                · linarith only [h1, h508, hlam]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h517 | h517
                                · rcases p488_3 (m.d 0 2) (by simp) with h518 | h518
                                  · rcases p488_3 (m.d 0 3) (by simp) with h519 | h519
                                    · linarith only [h4, h519, hlam]
                                    · rcases p488_3 (m.d 0 4) (by simp) with h521 | h521
                                      · linarith only [h5, h521, hlam]
                                      · rcases p488_3 (m.d 0 5) (by simp) with h523 | h523
                                        · linarith only [h523, h6, hlam]
                                        · linarith only [h301, h523, hlam]
                                  · linarith only [h5, h518, hlam]
                                · linarith only [h2, h517, hlam]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h528 | h528
                                · rcases p488_3 (m.d 0 2) (by simp) with h529 | h529
                                  · rcases p488_3 (m.d 0 3) (by simp) with h530 | h530
                                    · linarith only [h4, h530, hlam]
                                    · rcases p488_3 (m.d 0 4) (by simp) with h532 | h532
                                      · linarith only [h5, h532, hlam]
                                      · rcases p488_3 (m.d 0 5) (by simp) with h534 | h534
                                        · linarith only [h534, h6, hlam]
                                        · rcases h2bigk with h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h474, h481, h485, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1, u0elo1]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            rcases p536_3 (m.d 0 2) (by simp) with h539 | h539
                                            · rcases p536_3 (m.d 1 2) (by simp) with h540 | h540
                                              · linarith only [h0, h540, hlam]
                                              · linarith only [h472, h540, hlam]
                                            · linarith only [h539, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            rcases p536_3 (m.d 0 2) (by simp) with h544 | h544
                                            · rcases p536_3 (m.d 1 2) (by simp) with h545 | h545
                                              · linarith only [h0, h545, hlam]
                                              · linarith only [h473, h545, hlam]
                                            · linarith only [h544, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            rcases p536_3 (m.d 0 2) (by simp) with h549 | h549
                                            · rcases p536_3 (m.d 1 2) (by simp) with h550 | h550
                                              · linarith only [h0, h550, hlam]
                                              · linarith only [h474, h550, hlam]
                                            · linarith only [h549, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h0, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1, u0elo0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h0, h481, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1, u0elo0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h0, h481, h485, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1, u0elo0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h4, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h472, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h481, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h483, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h5, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h473, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1, u0elo0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h485, hlam, p536_1]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h6, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h474, hlam, p536_0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1, u0elo0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [h3, h474, hc24, hlam, hphi, ht0b, ht45, ht5b, p536_1, u0elo0]
                                          · have p536_0 := h536c.1
                                            have p536_1 := h536c.2.1
                                            have p536_2 := h536c.2.2.1
                                            have p536_3 := h536c.2.2.2
                                            linarith only [hlam, p536_0]
                                  · linarith only [h529, h6, hlam]
                                · linarith only [h3, h528, hlam]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h1, hlam, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h4, hlam, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h7, hlam, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h238, hlam, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h2, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h5, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h1, h301, h472, h487, hc23, hc34, hlam, hphi, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h301, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h3, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h6, hlam, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h1, h301, h472, h487, hc23, hc34, hlam, hphi, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h1, h301, h472, h487, h7, hc23, hc34, hlam, hphi, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                            · rcases h0bigk with h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h0, h474, hc25, hlam, hphi, ht0b, ht5b, p591_1, u0elo0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h594 | h594
                                · rcases p591_3 (m.d 0 2) (by simp) with h595 | h595
                                  · linarith only [h0, h595, hlam]
                                  · linarith only [h4, h595, hlam]
                                · linarith only [h1, h594, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h599 | h599
                                · rcases p591_3 (m.d 0 2) (by simp) with h600 | h600
                                  · linarith only [h0, h600, hlam]
                                  · linarith only [h5, h600, hlam]
                                · linarith only [h2, h599, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h604 | h604
                                · rcases p591_3 (m.d 0 2) (by simp) with h605 | h605
                                  · linarith only [h0, h605, hlam]
                                  · linarith only [h6, h605, hlam]
                                · linarith only [h3, h604, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h0, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h611 | h611
                                · rcases p591_3 (m.d 0 2) (by simp) with h612 | h612
                                  · rcases p591_3 (m.d 0 3) (by simp) with h613 | h613
                                    · linarith only [h4, h613, hlam]
                                    · rcases p591_3 (m.d 0 4) (by simp) with h615 | h615
                                      · linarith only [h5, h615, hlam]
                                      · linarith only [h615, h7, hlam]
                                  · linarith only [h4, h612, hlam]
                                · linarith only [h1, h611, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h620 | h620
                                · rcases p591_3 (m.d 0 2) (by simp) with h621 | h621
                                  · rcases p591_3 (m.d 0 3) (by simp) with h622 | h622
                                    · linarith only [h4, h622, hlam]
                                    · rcases p591_3 (m.d 0 4) (by simp) with h624 | h624
                                      · linarith only [h5, h624, hlam]
                                      · rcases p591_3 (m.d 0 5) (by simp) with h626 | h626
                                        · linarith only [h6, h626, hlam]
                                        · linarith only [h301, h626, hlam]
                                  · linarith only [h5, h621, hlam]
                                · linarith only [h2, h620, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h631 | h631
                                · rcases p591_3 (m.d 0 2) (by simp) with h632 | h632
                                  · rcases p591_3 (m.d 0 3) (by simp) with h633 | h633
                                    · linarith only [h4, h633, hlam]
                                    · rcases p591_3 (m.d 0 4) (by simp) with h635 | h635
                                      · linarith only [h5, h635, hlam]
                                      · rcases p591_3 (m.d 0 5) (by simp) with h637 | h637
                                        · linarith only [h6, h637, hlam]
                                        · rcases h2bigk with h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h0, h474, h481, h485, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p639_1, u0elo0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            rcases p639_3 (m.d 0 2) (by simp) with h642 | h642
                                            · rcases p639_3 (m.d 1 2) (by simp) with h643 | h643
                                              · linarith only [h0, h643, hlam]
                                              · linarith only [h472, h643, hlam]
                                            · linarith only [h642, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            rcases p639_3 (m.d 0 2) (by simp) with h647 | h647
                                            · rcases p639_3 (m.d 1 2) (by simp) with h648 | h648
                                              · linarith only [h0, h648, hlam]
                                              · linarith only [h473, h648, hlam]
                                            · linarith only [h647, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            rcases p639_3 (m.d 0 2) (by simp) with h652 | h652
                                            · rcases p639_3 (m.d 1 2) (by simp) with h653 | h653
                                              · linarith only [h0, h653, hlam]
                                              · linarith only [h474, h653, hlam]
                                            · linarith only [h652, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h0, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p639_1, u0elo0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h0, h481, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p639_1, u0elo0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h0, h481, h485, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p639_1, u0elo0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h4, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h472, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h481, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h483, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h5, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h473, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p639_1, u0elo0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h485, hlam, p639_1]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h6, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h474, hlam, p639_0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h0, h3, h474, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p591_1, p639_1, u0elo0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [h0, h3, h474, hc24, hlam, hphi, ht0b, ht45, ht5b, p591_1, p639_1, u0elo0]
                                          · have p639_0 := h639c.1
                                            have p639_1 := h639c.2.1
                                            have p639_2 := h639c.2.2.1
                                            have p639_3 := h639c.2.2.2
                                            linarith only [hlam, p639_0]
                                  · linarith only [h6, h632, hlam]
                                · linarith only [h3, h631, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h1, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h4, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h7, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h238, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h2, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h5, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h1, h472, h487, h7, hc23, hc45, hlam, hphi, ht34, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h301, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h3, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h6, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h691 | h691
                                · rcases p591_3 (m.d 0 2) (by simp) with h692 | h692
                                  · rcases p591_3 (m.d 0 3) (by simp) with h693 | h693
                                    · linarith only [h238, h693, hlam]
                                    · rcases p591_3 (m.d 0 4) (by simp) with h695 | h695
                                      · linarith only [h301, h695, hlam]
                                      · linarith only [h695, h7, hlam]
                                  · linarith only [h4, h692, hlam]
                                · linarith only [h1, h691, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h700 | h700
                                · rcases p591_3 (m.d 0 2) (by simp) with h701 | h701
                                  · rcases p591_3 (m.d 0 3) (by simp) with h702 | h702
                                    · linarith only [h238, h702, hlam]
                                    · rcases p591_3 (m.d 0 4) (by simp) with h704 | h704
                                      · linarith only [h301, h704, hlam]
                                      · rcases p591_3 (m.d 0 5) (by simp) with h706 | h706
                                        · rcases h2bigk with h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h0, h474, hc25, hlam, hphi, ht0b, ht5b, p707_1, u0elo0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            rcases p707_3 (m.d 0 2) (by simp) with h710 | h710
                                            · rcases p707_3 (m.d 1 2) (by simp) with h711 | h711
                                              · linarith only [h0, h711, hlam]
                                              · linarith only [h472, h711, hlam]
                                            · linarith only [h710, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            rcases p707_3 (m.d 0 2) (by simp) with h715 | h715
                                            · rcases p707_3 (m.d 1 2) (by simp) with h716 | h716
                                              · linarith only [h0, h716, hlam]
                                              · linarith only [h473, h716, hlam]
                                            · linarith only [h715, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            rcases p707_3 (m.d 0 2) (by simp) with h720 | h720
                                            · rcases p707_3 (m.d 1 2) (by simp) with h721 | h721
                                              · linarith only [h0, h721, hlam]
                                              · linarith only [h474, h721, hlam]
                                            · linarith only [h720, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h0, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p707_1, u0elo0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h0, h481, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p707_1, u0elo0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h0, h481, h485, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p707_1, u0elo0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h4, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h472, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h481, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h483, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h5, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h473, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p707_1, u0elo0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h485, hlam, p707_1]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h6, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h474, hlam, p707_0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p707_1, u0elo0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [h0, h474, hc24, hlam, hphi, ht0b, ht45, ht5b, p707_1, u0elo0]
                                          · have p707_0 := h707c.1
                                            have p707_1 := h707c.2.1
                                            have p707_2 := h707c.2.2.1
                                            have p707_3 := h707c.2.2.2
                                            linarith only [hlam, p707_0]
                                        · linarith only [h301, h706, hlam]
                                  · linarith only [h5, h701, hlam]
                                · linarith only [h2, h700, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
              · linarith only [h0, h472, h474, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h472, h473, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h751 | h751
            · linarith only [h0, h4, h472, h751, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h753 | h753
              · linarith only [h0, h4, h472, h753, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h755 | h755
                · linarith only [h0, h4, h472, h7, h755, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h757 | h757
                  · linarith only [h1, h238, h4, h472, h757, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h759 | h759
                    · linarith only [h2, h301, h759, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h761 | h761
                      · linarith only [h4, h7, h761, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h763 | h763
                        · linarith only [h238, h4, h763, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h765 | h765
                          · linarith only [h0, h301, h4, h472, h5, h7, h765, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h767 | h767
                            · linarith only [h301, h4, h472, h7, h767, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h4, h472, h7, h767, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h770 | h770
    · rcases m.htr 0 3 5 (by decide) (by decide) with h771 | h771
      · linarith only [h4, h6, h771, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h773 | h773
        · linarith only [h4, h6, h770, h773, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h775 | h775
          · rcases m.htr 1 2 4 (by decide) (by decide) with h776 | h776
            · rcases m.htr 1 2 5 (by decide) (by decide) with h777 | h777
              · linarith only [h0, h6, h777, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h779 | h779
                · rcases m.htr 1 3 5 (by decide) (by decide) with h780 | h780
                  · linarith only [h1, h771, h780, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h782 | h782
                    · linarith only [h2, h773, h782, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h784 | h784
                      · linarith only [h0, h775, h784, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h771, h779, h784, hc23, hc35, hlam, hphi]
                · linarith only [h770, h771, h779, hc13, hc35, hlam, hphi]
            · linarith only [h5, h6, h776, hc12, hc25, hlam, hphi]
          · linarith only [h4, h6, h775, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h790 | h790
      · linarith only [h5, h6, h770, h790, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h792 | h792
        · linarith only [h5, h6, h792, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h794 | h794
          · rcases m.htr 1 2 4 (by decide) (by decide) with h795 | h795
            · rcases m.htr 1 2 5 (by decide) (by decide) with h796 | h796
              · linarith only [h0, h6, h796, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h798 | h798
                · linarith only [h1, h770, h798, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h800 | h800
                  · linarith only [h0, h1, h6, h770, h790, h794, h800, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h802 | h802
                    · linarith only [h2, h792, h802, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h804 | h804
                      · linarith only [h0, h794, h804, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h806 | h806
                        · linarith only [h3, h790, h795, h796, h804, h806, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h808 | h808
                          · linarith only [h3, h792, h795, h796, h808, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h810 | h810
                            · linarith only [h4, h6, h808, h810, hc23, hc34, hlam, hphi]
                            · rcases h0bigk with h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [hlam, p812_0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h0, h795, h804, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p812_1, u0elo0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                rcases p812_3 (m.d 0 1) (by simp) with h815 | h815
                                · rcases p812_3 (m.d 0 2) (by simp) with h816 | h816
                                  · linarith only [h0, h816, hlam]
                                  · linarith only [h4, h816, hlam]
                                · linarith only [h1, h815, hlam]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                rcases p812_3 (m.d 0 1) (by simp) with h820 | h820
                                · rcases p812_3 (m.d 0 2) (by simp) with h821 | h821
                                  · linarith only [h0, h821, hlam]
                                  · linarith only [h5, h821, hlam]
                                · linarith only [h2, h820, hlam]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h0, h6, h795, h804, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p812_1, u0elo0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h0, hlam, p812_0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [hlam, p812_0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h1, h6, h794, h806, hc23, hc35, hlam, hphi, p812_1]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h1, h6, h770, h794, h806, hc23, hc35, hlam, hphi, p812_1]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h6, hlam, p812_0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h1, hlam, p812_1]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h4, hlam, p812_1]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [hlam, p812_0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h770, hlam, p812_1]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h790, hlam, p812_1]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h2, hlam, p812_0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h5, hlam, p812_0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h1, h5, h6, h794, h806, hc23, hc35, hlam, hphi, p812_1]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [hlam, p812_0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h792, hlam, p812_0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h3, hlam, p812_0]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [h0, h795, h804, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p812_1, u0elo4]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                rcases p812_3 (m.d 0 1) (by simp) with h843 | h843
                                · rcases p812_3 (m.d 0 2) (by simp) with h844 | h844
                                  · linarith only [h6, h844, hlam]
                                  · linarith only [h4, h844, hlam]
                                · linarith only [h1, h843, hlam]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                rcases p812_3 (m.d 0 1) (by simp) with h848 | h848
                                · rcases p812_3 (m.d 0 2) (by simp) with h849 | h849
                                  · linarith only [h6, h849, hlam]
                                  · linarith only [h5, h849, hlam]
                                · linarith only [h2, h848, hlam]
                              · have p812_0 := h812c.1
                                have p812_1 := h812c.2.1
                                have p812_2 := h812c.2.2.1
                                have p812_3 := h812c.2.2.2
                                linarith only [hlam, p812_0]
            · linarith only [h5, h6, h795, hc12, hc25, hlam, hphi]
          · linarith only [h4, h6, h794, hc12, hc25, hlam, hphi]

end R2N4
