import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6014000 in
set_option maxHeartbeats 6014000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
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
                                · linarith only [h16, h7, hc23, hlam, hphi, u3elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                                · linarith only [h0, h10, h19, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h19, h7, hc23, hlam, hphi, u3elo0]
                            · linarith only [h14, h8, hc13, hlam, hphi, u3elo0]
                          · linarith only [h10, h13, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                      · linarith only [h0, h10, h26, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h0, h10, h28, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                                      · linarith only [h1, h30, h36, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                      · linarith only [h2, h32, h36, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · linarith only [h26, h32, h35, hlam]
                                  · linarith only [h10, h31, h34, hlam]
                                · linarith only [h10, h33, h7, hc13, hlam, hphi, u3elo0]
                              · linarith only [h26, h32, h7, h9, hc12, hlam, hphi, ht23, u3elo0]
                            · linarith only [h30, h31, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · linarith only [h10, h30, h7, hc12, hlam, hphi, ht23, u3elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                              · linarith only [h2, h50, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                                · linarith only [h0, h45, h52, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h52, h7, hc23, hlam, hphi, u3elo0]
                            · linarith only [h49, h8, hc13, hlam, hphi, u3elo0]
                          · linarith only [h45, h48, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h0, h46, h47, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h45, h46, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                      · linarith only [h0, h4, h45, h59, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                        · linarith only [h0, h4, h45, h61, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                              · linarith only [h5, h59, h63, h65, h9, hc12, hlam, hphi, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                                    · linarith only [h5, h69, h9, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                                      · linarith only [h5, h59, h71, h9, hc12, hlam, hphi, ht23, u3elo3]
                                      · rcases h0bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h4, h45, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p73_1, u0elo0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h1, h64, h71, hc34, hlam, hphi, ht0b, ht45, ht5b, p73_1, u0elo0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h5, h59, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p73_1, u0elo0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h5, h59, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p73_1, u0elo0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h0, hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h5, h59, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p73_1, u0elo1]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h0, h5, h59, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p73_1, u0elo0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h0, h5, h59, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p73_1, u0elo0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h1, hlam, p73_1]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h4, hlam, p73_1]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h5, h59, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p73_1, u0elo2]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h5, h59, h9, hc12, hlam, hphi, ht23, p73_1, u3elo0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h2, hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h5, hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h7, hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h9, hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h3, hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h6, hlam, p73_1]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h8, hlam, p73_0]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [h5, h59, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p73_1, u0elo4]
                                        · have p73_0 := h73c.1
                                          have p73_1 := h73c.2.1
                                          have p73_2 := h73c.2.2.1
                                          have p73_3 := h73c.2.2.2
                                          linarith only [hlam, p73_0]
                                  · linarith only [h45, h64, h68, hlam]
                                · linarith only [h45, h67, h7, hc13, hlam, hphi, u3elo0]
                            · linarith only [h64, h8, hc13, hlam, hphi, u3elo0]
                          · linarith only [h45, h63, h7, hc12, hlam, hphi, ht23, u3elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
                  · linarith only [h103, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
                            · linarith only [h1, h109, h8, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                              · linarith only [h103, h111, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                                · linarith only [h0, h105, h113, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h1, h108, h113, h8, hc23, hlam, hphi, u3elo4]
                          · linarith only [h108, h7, h8, hc13, hlam, hphi, u3elo4]
                        · linarith only [h0, h105, h107, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h105, h106, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h105, h4, h8, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h120 | h120
                · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h125 | h125
                          · linarith only [h125, h7, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h127 | h127
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h128 | h128
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h129 | h129
                                · linarith only [h0, h1, h122, h127, h129, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                                  · linarith only [h0, h123, h129, h131, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h1, h127, h131, h7, hc23, hlam, hphi, u3elo3]
                              · linarith only [h121, h125, h127, h128, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h120, h127, h7, hc13, hlam, hphi, u3elo3]
                        · linarith only [h120, h124, h6, h7, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h0, h122, h123, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h122, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h120, h121, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h140 | h140
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h143 | h143
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
                          · linarith only [h144, h7, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                            · linarith only [h1, h120, h146, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h148 | h148
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
                                · linarith only [h1, h141, h149, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h151 | h151
                                  · linarith only [h1, h120, h141, h151, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h153 | h153
                                    · linarith only [h0, h142, h153, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h148, h153, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h140, h141, h144, h148, h7, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h141, h143, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h141, h142, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h141, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h161 | h161
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h162 | h162
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                          · linarith only [h1, h163, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h165 | h165
                            · linarith only [h1, h120, h165, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h167 | h167
                              · linarith only [h1, h140, h160, h167, h2, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                                · linarith only [h1, h160, h169, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h171 | h171
                                  · linarith only [h1, h120, h160, h171, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
                                    · linarith only [h140, h161, h173, h2, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
                                      · linarith only [h1, h140, h160, h175, h7, hc23, hlam, hphi, u3elo3]
                                      · rcases h0bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [hlam, p177_0]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h0, h162, hc25, hlam, hphi, ht0b, ht5b, p177_1, u0elo0]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          rcases p177_3 (m.d 0 1) (by simp) with h180 | h180
                                          · rcases p177_3 (m.d 0 2) (by simp) with h181 | h181
                                            · linarith only [h0, h181, hlam]
                                            · linarith only [h181, h4, hlam]
                                          · linarith only [h1, h180, hlam]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          rcases p177_3 (m.d 0 1) (by simp) with h185 | h185
                                          · rcases p177_3 (m.d 0 2) (by simp) with h186 | h186
                                            · linarith only [h0, h186, hlam]
                                            · linarith only [h186, h5, hlam]
                                          · linarith only [h185, h2, hlam]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          rcases p177_3 (m.d 0 1) (by simp) with h190 | h190
                                          · rcases p177_3 (m.d 0 2) (by simp) with h191 | h191
                                            · linarith only [h0, h191, hlam]
                                            · linarith only [h191, h6, hlam]
                                          · linarith only [h190, h3, hlam]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h0, hlam, p177_0]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [hlam, p177_0]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          rcases p177_3 (m.d 0 1) (by simp) with h197 | h197
                                          · rcases p177_3 (m.d 0 2) (by simp) with h198 | h198
                                            · rcases p177_3 (m.d 0 3) (by simp) with h199 | h199
                                              · linarith only [h199, h4, hlam]
                                              · rcases p177_3 (m.d 0 4) (by simp) with h201 | h201
                                                · linarith only [h201, h5, hlam]
                                                · linarith only [h201, h7, hlam]
                                            · linarith only [h198, h4, hlam]
                                          · linarith only [h1, h197, hlam]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          rcases p177_3 (m.d 0 1) (by simp) with h206 | h206
                                          · rcases p177_3 (m.d 0 2) (by simp) with h207 | h207
                                            · rcases p177_3 (m.d 0 3) (by simp) with h208 | h208
                                              · linarith only [h208, h4, hlam]
                                              · rcases p177_3 (m.d 0 4) (by simp) with h210 | h210
                                                · linarith only [h210, h5, hlam]
                                                · rcases p177_3 (m.d 0 5) (by simp) with h212 | h212
                                                  · linarith only [h212, h6, hlam]
                                                  · linarith only [h140, h212, hlam]
                                            · linarith only [h207, h5, hlam]
                                          · linarith only [h2, h206, hlam]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          rcases p177_3 (m.d 0 1) (by simp) with h217 | h217
                                          · rcases p177_3 (m.d 0 2) (by simp) with h218 | h218
                                            · rcases p177_3 (m.d 0 3) (by simp) with h219 | h219
                                              · linarith only [h219, h4, hlam]
                                              · rcases p177_3 (m.d 0 4) (by simp) with h221 | h221
                                                · linarith only [h221, h5, hlam]
                                                · rcases p177_3 (m.d 0 5) (by simp) with h223 | h223
                                                  · linarith only [h223, h6, hlam]
                                                  · rcases h2bigk with h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h162, h169, h173, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p225_1, u0elo1]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      rcases p225_3 (m.d 0 2) (by simp) with h228 | h228
                                                      · rcases p225_3 (m.d 1 2) (by simp) with h229 | h229
                                                        · linarith only [h0, h229, hlam]
                                                        · linarith only [h160, h229, hlam]
                                                      · linarith only [h228, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      rcases p225_3 (m.d 0 2) (by simp) with h233 | h233
                                                      · rcases p225_3 (m.d 1 2) (by simp) with h234 | h234
                                                        · linarith only [h0, h234, hlam]
                                                        · linarith only [h161, h234, hlam]
                                                      · linarith only [h233, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      rcases p225_3 (m.d 0 2) (by simp) with h238 | h238
                                                      · rcases p225_3 (m.d 1 2) (by simp) with h239 | h239
                                                        · linarith only [h0, h239, hlam]
                                                        · linarith only [h162, h239, hlam]
                                                      · linarith only [h238, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h0, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p225_1, u0elo0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h0, h169, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p225_1, u0elo0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h0, h169, h173, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p225_1, u0elo0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h4, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h160, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h169, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h171, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h5, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h161, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p225_1, u0elo0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h173, hlam, p225_1]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h6, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h162, hlam, p225_0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p225_1, u0elo0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [h162, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, p225_1, u0elo0]
                                                    · have p225_0 := h225c.1
                                                      have p225_1 := h225c.2.1
                                                      have p225_2 := h225c.2.2.1
                                                      have p225_3 := h225c.2.2.2
                                                      linarith only [hlam, p225_0]
                                            · linarith only [h218, h6, hlam]
                                          · linarith only [h217, h3, hlam]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h1, hlam, p177_1]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h4, hlam, p177_1]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [hlam, p177_0]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h7, hlam, p177_1]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h120, hlam, p177_1]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h2, hlam, p177_0]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h5, hlam, p177_0]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h1, h160, h7, hc23, hlam, hphi, p177_1, u3elo3]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [hlam, p177_0]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h140, hlam, p177_0]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h3, hlam, p177_0]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h6, hlam, p177_1]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h1, h120, h160, hc23, hlam, hphi, p177_1, u3elo4]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [h1, h120, h160, h7, hc23, hlam, hphi, p177_1, u3elo4]
                                        · have p177_0 := h177c.1
                                          have p177_1 := h177c.2.1
                                          have p177_2 := h177c.2.2.1
                                          have p177_3 := h177c.2.2.2
                                          linarith only [hlam, p177_0]
                        · linarith only [h0, h160, h162, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h160, h161, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h160, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h283 | h283
              · rcases m.htr 0 3 5 (by decide) (by decide) with h284 | h284
                · linarith only [h284, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
                  · linarith only [h283, h286, h4, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h289 | h289
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h290 | h290
                        · linarith only [h0, h290, h6, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h292 | h292
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h293 | h293
                            · linarith only [h1, h284, h293, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                              · linarith only [h2, h286, h295, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h297 | h297
                                · linarith only [h0, h288, h297, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h1, h284, h292, h297, hc23, hlam, hphi, u3elo4]
                          · linarith only [h283, h284, h292, hc13, hlam, hphi, u3elo4]
                      · linarith only [h289, h5, h6, hc12, hc25, hlam, hphi]
                    · linarith only [h284, h288, h4, h6, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h303 | h303
                · linarith only [h283, h303, h4, h6, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h305 | h305
                  · linarith only [h305, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h308 | h308
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h309 | h309
                        · linarith only [h0, h309, h6, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h311 | h311
                          · linarith only [h283, h311, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h313 | h313
                            · linarith only [h0, h1, h283, h303, h307, h313, h6, hc23, hlam, hphi, u3elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
                              · linarith only [h2, h305, h315, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
                                · linarith only [h0, h283, h307, h317, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h319 | h319
                                  · linarith only [h1, h283, h303, h307, h319, h6, hc02, hlam, hphi, ht23, u3elo3]
                                  · linarith only [h0, h308, h317, h319, h6, hc23, hlam, hphi, u3elo4]
                      · linarith only [h307, h308, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h303, h307, h4, h6, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h324 | h324
            · rcases m.htr 0 3 4 (by decide) (by decide) with h325 | h325
              · linarith only [h325, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h327 | h327
                · rcases m.htr 0 4 5 (by decide) (by decide) with h328 | h328
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h330 | h330
                      · linarith only [h0, h330, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h332 | h332
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h333 | h333
                          · linarith only [h1, h325, h333, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h335 | h335
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h336 | h336
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                                · linarith only [h2, h325, h329, h330, h337, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                                · linarith only [h0, h329, h337, h5, hc23, hlam, hphi, u3elo3]
                              · linarith only [h325, h327, h328, h329, h330, h336, hc23, hlam, hphi, u3elo3]
                            · linarith only [h325, h327, h335, hc13, hlam, hphi, u3elo3]
                        · linarith only [h324, h329, h332, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h325, h329, h4, h5, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h325, h327, h328, h4, h5, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h346 | h346
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h347 | h347
                      · linarith only [h0, h347, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h349 | h349
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h350 | h350
                          · linarith only [h1, h325, h350, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h352 | h352
                            · linarith only [h1, h327, h352, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h354 | h354
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                                · linarith only [h0, h325, h346, h355, h5, hlam]
                                · linarith only [h0, h346, h355, h5, hc23, hlam, hphi, u3elo3]
                              · linarith only [h325, h345, h346, h347, h354, hc23, hlam, hphi, u3elo3]
                        · linarith only [h324, h346, h349, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h325, h346, h4, h5, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h324, h345, h5, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h362 | h362
              · linarith only [h362, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h364 | h364
                · linarith only [h324, h362, h364, h4, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h366 | h366
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h368 | h368
                      · linarith only [h0, h368, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h370 | h370
                        · linarith only [h0, h324, h370, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                          · linarith only [h362, h372, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                            · linarith only [h0, h1, h324, h364, h367, h374, hc23, hlam, hphi, u3elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h376 | h376
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h377 | h377
                                · linarith only [h0, h362, h367, h377, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h377, h4, h5, hc23, hlam, hphi, u3elo3]
                              · linarith only [h366, h367, h368, h376, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h367, h4, h5, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h382 | h382
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h383 | h383
                      · linarith only [h0, h383, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h385 | h385
                        · linarith only [h0, h324, h385, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h387 | h387
                          · linarith only [h1, h362, h387, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h389 | h389
                            · linarith only [h1, h2, h362, h364, h366, h382, h383, h389, hc23, hlam, hphi, u3elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h391 | h391
                              · linarith only [h2, h366, h391, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
                                · linarith only [h0, h362, h382, h393, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h393, h4, h5, hc23, hlam, hphi, u3elo3]
                    · linarith only [h382, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h397 | h397
          · rcases m.htr 0 2 5 (by decide) (by decide) with h398 | h398
            · rcases m.htr 0 3 4 (by decide) (by decide) with h399 | h399
              · rcases m.htr 0 3 5 (by decide) (by decide) with h400 | h400
                · rcases m.htr 0 4 5 (by decide) (by decide) with h401 | h401
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h402 | h402
                    · linarith only [h0, h4, h402, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h409 | h409
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h410 | h410
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h411 | h411
                                    · linarith only [h0, h4, h404, h411, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                    · linarith only [h397, h4, h401, h409, h411, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · linarith only [h4, h410, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h4, h409, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h397, h4, h401, h408, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h400, h402, h405, h407, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h399, h4, h402, h404, h406, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h398, h404, h405, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h397, h4, h404, hc12, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
                    · linarith only [h0, h4, h421, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h424 | h424
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h425 | h425
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h426 | h426
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h427 | h427
                              · linarith only [h2, h401, h427, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h429 | h429
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h430 | h430
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h431 | h431
                                    · linarith only [h2, h401, h423, h431, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                                      · linarith only [h2, h401, h423, h429, h433, hlam]
                                      · rcases h0bigk with h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h0, h424, h429, h431, hc34, hlam, hphi, ht0b, ht45, ht5b, p435_1, u0elo0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h1, h421, h424, h429, h431, hc34, hlam, hphi, ht0b, ht45, ht5b, p435_1, u0elo0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          rcases p435_3 (m.d 0 1) (by simp) with h439 | h439
                                          · rcases p435_3 (m.d 0 2) (by simp) with h440 | h440
                                            · linarith only [h0, h440, hlam]
                                            · linarith only [h397, h440, hlam]
                                          · linarith only [h2, h439, hlam]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          rcases p435_3 (m.d 0 1) (by simp) with h444 | h444
                                          · rcases p435_3 (m.d 0 2) (by simp) with h445 | h445
                                            · linarith only [h0, h445, hlam]
                                            · linarith only [h398, h445, hlam]
                                          · linarith only [h3, h444, hlam]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h0, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h4, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h2, h4, h423, h429, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p435_1, u3elo2]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h2, h4, h401, h423, h429, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p435_1, u3elo2]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h1, hlam, p435_1]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hc02, hlam, hphi, ht23, p435_1, u3elo0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          rcases p435_3 (m.d 0 1) (by simp) with h457 | h457
                                          · rcases p435_3 (m.d 0 2) (by simp) with h458 | h458
                                            · linarith only [h4, h458, hlam]
                                            · linarith only [h397, h458, hlam]
                                          · linarith only [h2, h457, hlam]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          rcases p435_3 (m.d 0 1) (by simp) with h462 | h462
                                          · rcases p435_3 (m.d 0 2) (by simp) with h463 | h463
                                            · linarith only [h4, h463, hlam]
                                            · linarith only [h398, h463, hlam]
                                          · linarith only [h3, h462, hlam]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h2, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h397, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h399, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h401, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h3, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h398, hlam, p435_1]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h400, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h2, h398, h4, h423, h429, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p435_1, u3elo2]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hlam, p435_0]
                                  · linarith only [h4, h430, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h0, h4, h423, h429, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h400, h421, h423, h426, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h399, h421, h423, h425, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h398, h423, h424, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h397, h4, h423, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h398, h4, h400, hlam]
              · linarith only [h397, h399, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h485 | h485
              · rcases m.htr 0 3 5 (by decide) (by decide) with h486 | h486
                · rcases m.htr 0 4 5 (by decide) (by decide) with h487 | h487
                  · linarith only [h397, h398, h487, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
                    · linarith only [h0, h4, h489, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                        · linarith only [h398, h489, h492, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h496 | h496
                              · linarith only [h2, h487, h496, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h498 | h498
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h499 | h499
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h500 | h500
                                    · linarith only [h0, h398, h487, h491, h500, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h502 | h502
                                      · linarith only [h0, h398, h491, h498, h500, h502, hlam]
                                      · rcases h0bigk with h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h0, h491, h498, hc34, hlam, hphi, ht0b, ht45, ht5b, p504_1, u0elo0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h0, h398, h486, h491, h498, hc34, hlam, hphi, ht0b, ht45, ht5b, p504_1, u0elo0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          rcases p504_3 (m.d 0 1) (by simp) with h508 | h508
                                          · rcases p504_3 (m.d 0 2) (by simp) with h509 | h509
                                            · linarith only [h0, h509, hlam]
                                            · linarith only [h397, h509, hlam]
                                          · linarith only [h2, h508, hlam]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h0, h398, h491, h498, hc34, hlam, hphi, ht0b, ht45, ht5b, p504_1, u0elo0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h0, hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h4, hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h2, h398, h491, h498, h500, hc34, hc45, hlam, hphi, p504_1]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h398, hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h1, hlam, p504_1]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [hc02, hlam, hphi, ht23, p504_1, u3elo0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          rcases p504_3 (m.d 0 1) (by simp) with h522 | h522
                                          · rcases p504_3 (m.d 0 2) (by simp) with h523 | h523
                                            · linarith only [h4, h523, hlam]
                                            · linarith only [h397, h523, hlam]
                                          · linarith only [h2, h522, hlam]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h0, h398, h491, h498, hc34, hlam, hphi, ht0b, ht45, ht5b, p504_1, u0elo2]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h2, hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h397, hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h485, hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h487, hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h3, hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h0, h491, h498, hc34, hlam, hphi, ht0b, ht45, ht5b, p504_1, u0elo4]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [h486, hlam, p504_0]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          rcases p504_3 (m.d 0 1) (by simp) with h536 | h536
                                          · rcases p504_3 (m.d 0 2) (by simp) with h537 | h537
                                            · linarith only [h398, h537, hlam]
                                            · linarith only [h397, h537, hlam]
                                          · linarith only [h2, h536, hlam]
                                        · have p504_0 := h504c.1
                                          have p504_1 := h504c.2.1
                                          have p504_2 := h504c.2.2.1
                                          have p504_3 := h504c.2.2.2
                                          linarith only [hlam, p504_0]
                                  · linarith only [h1, h4, h495, h499, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                                · linarith only [h4, h498, hc02, hlam, hphi, ht23, u3elo3]
                            · linarith only [h486, h489, h491, h495, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h4, h485, h489, h491, h494, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h397, h4, h491, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h547 | h547
                  · linarith only [h397, h4, h486, h547, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h549 | h549
                    · linarith only [h0, h4, h486, h549, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h551 | h551
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h552 | h552
                        · linarith only [h0, h398, h552, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h555 | h555
                            · linarith only [h0, h4, h486, h551, h555, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h557 | h557
                              · linarith only [h2, h547, h557, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h559 | h559
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h560 | h560
                                  · linarith only [h0, h4, h486, h551, h559, h560, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · linarith only [h0, h4, h551, h559, h560, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h0, h4, h551, h559, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h485, h486, h554, hc13, hlam, hphi, u3elo4]
                      · linarith only [h397, h4, h551, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h397, h4, h485, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h567 | h567
            · rcases m.htr 0 3 4 (by decide) (by decide) with h568 | h568
              · rcases m.htr 0 3 5 (by decide) (by decide) with h569 | h569
                · rcases m.htr 0 4 5 (by decide) (by decide) with h570 | h570
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h571 | h571
                    · linarith only [h0, h4, h571, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h573 | h573
                      · linarith only [h397, h571, h573, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h575 | h575
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h576 | h576
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h577 | h577
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h578 | h578
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h579 | h579
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h580 | h580
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h581 | h581
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h582 | h582
                                      · linarith only [h1, h576, h582, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                      · linarith only [h1, h576, h578, h582, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · linarith only [h1, h397, h576, h578, h581, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                  · linarith only [h0, h397, h575, h579, h580, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                                · linarith only [h0, h4, h575, h579, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h4, h567, h570, h573, h575, h578, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · linarith only [h4, h569, h577, hc13, hlam, hphi, u3elo2]
                          · linarith only [h4, h568, h571, h575, h576, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · linarith only [h397, h567, h575, hc12, hc24, hlam, hphi]
                  · linarith only [h397, h567, h570, hlam]
                · linarith only [h397, h567, h568, h569, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h594 | h594
                · rcases m.htr 0 4 5 (by decide) (by decide) with h595 | h595
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h596 | h596
                    · linarith only [h0, h4, h596, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h598 | h598
                      · linarith only [h0, h397, h598, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h600 | h600
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h601 | h601
                          · linarith only [h1, h568, h601, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h603 | h603
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h604 | h604
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h605 | h605
                                · linarith only [h1, h568, h596, h600, h605, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                · linarith only [h0, h4, h600, h605, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h595, h596, h600, h601, h604, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h594, h596, h600, h603, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h4, h567, h600, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h397, h567, h595, hlam]
                · linarith only [h4, h567, h594, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h613 | h613
              · rcases m.htr 0 3 5 (by decide) (by decide) with h614 | h614
                · rcases m.htr 0 4 5 (by decide) (by decide) with h615 | h615
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h616 | h616
                    · linarith only [h0, h4, h616, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h618 | h618
                      · linarith only [h397, h616, h618, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h620 | h620
                        · linarith only [h0, h567, h620, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h622 | h622
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h623 | h623
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h624 | h624
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h625 | h625
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h626 | h626
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h627 | h627
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h628 | h628
                                      · linarith only [h1, h622, h628, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                      · linarith only [h2, h624, h628, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · linarith only [h0, h3, h397, h624, h627, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                  · linarith only [h0, h397, h625, h626, hc12, hlam, hphi, ht23, u3elo4]
                                · linarith only [h1, h622, h625, hc23, hlam, hphi, u3elo0]
                              · linarith only [h613, h615, h618, h624, hc12, hlam, hphi, ht23, u3elo0]
                            · linarith only [h4, h614, h622, h623, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h4, h613, h616, h622, hc12, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
                    · linarith only [h0, h4, h613, h637, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h639 | h639
                      · linarith only [h397, h637, h639, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h641 | h641
                        · linarith only [h0, h567, h641, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h643 | h643
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h644 | h644
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h645 | h645
                              · linarith only [h2, h615, h645, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h647 | h647
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h648 | h648
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h649 | h649
                                    · linarith only [h0, h397, h615, h647, h649, hc12, hlam, hphi, ht23, u3elo2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h651 | h651
                                      · linarith only [h1, h643, h649, h651, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                      · rcases h0bigk with h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          rcases p653_3 (m.d 0 1) (by simp) with h655 | h655
                                          · rcases p653_3 (m.d 0 2) (by simp) with h656 | h656
                                            · linarith only [h0, h656, hlam]
                                            · rcases p653_3 (m.d 0 3) (by simp) with h658 | h658
                                              · linarith only [h1, h658, hlam]
                                              · linarith only [h4, h658, hlam]
                                          · linarith only [h0, h655, hlam]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h1, h644, h651, hc34, hlam, hphi, ht0b, ht45, ht5b, p653_1, u0elo0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          rcases p653_3 (m.d 0 1) (by simp) with h663 | h663
                                          · rcases p653_3 (m.d 0 2) (by simp) with h664 | h664
                                            · linarith only [h0, h664, hlam]
                                            · rcases p653_3 (m.d 0 3) (by simp) with h666 | h666
                                              · linarith only [h1, h666, hlam]
                                              · linarith only [h613, h666, hlam]
                                          · linarith only [h2, h663, hlam]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          rcases p653_3 (m.d 0 1) (by simp) with h670 | h670
                                          · rcases p653_3 (m.d 0 2) (by simp) with h671 | h671
                                            · linarith only [h0, h671, hlam]
                                            · rcases p653_3 (m.d 0 3) (by simp) with h673 | h673
                                              · linarith only [h1, h673, hlam]
                                              · linarith only [h614, h673, hlam]
                                          · linarith only [h3, h670, hlam]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h0, hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h4, hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h397, hlam, p653_1]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h567, hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h1, hlam, p653_1]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, ht23, p653_1, u3elo0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h0, h397, h4, hc12, hlam, hphi, ht23, p653_1, u3elo2]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h0, h397, h4, h615, hc12, hlam, hphi, ht23, p653_1, u3elo2]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h2, hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h0, h397, h649, hc12, hc45, hlam, hphi, ht23, ht34, p653_1]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h613, hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h615, hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h3, hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h0, h4, h614, hc12, hlam, hphi, ht23, p653_1, u3elo2]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h614, hlam, p653_0]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [h2, h4, h614, h639, hc12, hlam, hphi, ht23, p653_1, u3elo2]
                                        · have p653_0 := h653c.1
                                          have p653_1 := h653c.2.1
                                          have p653_2 := h653c.2.2.1
                                          have p653_3 := h653c.2.2.2
                                          linarith only [hlam, p653_0]
                                  · linarith only [h0, h4, h648, hc12, hlam, hphi, ht23, u3elo4]
                                · linarith only [h0, h1, h4, h643, h647, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h4, h614, h644, hc13, hlam, hphi, u3elo2]
                          · linarith only [h4, h613, h637, h643, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h701 | h701
                  · linarith only [h613, h614, h701, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h703 | h703
                    · linarith only [h0, h4, h703, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h705 | h705
                      · linarith only [h397, h703, h705, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h707 | h707
                        · linarith only [h0, h567, h707, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h709 | h709
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h710 | h710
                            · linarith only [h1, h614, h710, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h712 | h712
                              · linarith only [h2, h701, h712, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h714 | h714
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h715 | h715
                                  · linarith only [h1, h614, h709, h715, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · linarith only [h0, h4, h715, hc12, hlam, hphi, ht23, u3elo4]
                                · linarith only [h0, h1, h4, h709, h714, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h613, h614, h709, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h720 | h720
                · rcases m.htr 0 4 5 (by decide) (by decide) with h721 | h721
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h722 | h722
                    · linarith only [h0, h4, h722, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h724 | h724
                      · linarith only [h0, h397, h724, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h726 | h726
                        · linarith only [h0, h567, h726, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h728 | h728
                          · linarith only [h1, h613, h728, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h730 | h730
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h731 | h731
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h732 | h732
                                · linarith only [h567, h613, h720, h732, hc02, hlam, hphi, ht23, u3elo2]
                                · linarith only [h0, h4, h732, hc12, hlam, hphi, ht23, u3elo3]
                              · linarith only [h721, h728, h730, h731, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h720, h730, hc13, hlam, hphi, u3elo0]
                  · linarith only [h613, h720, h721, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h738 | h738
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h739 | h739
                    · linarith only [h0, h4, h739, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h741 | h741
                      · linarith only [h397, h739, h741, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h743 | h743
                        · linarith only [h0, h567, h743, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h745 | h745
                          · linarith only [h1, h613, h745, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h747 | h747
                            · linarith only [h1, h720, h747, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h749 | h749
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h750 | h750
                                · linarith only [h613, h750, hc03, hlam, hphi, u3elo2]
                                · linarith only [h0, h4, h750, hc12, hlam, hphi, ht23, u3elo3]
                              · linarith only [h613, h738, h741, h749, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h754 | h754
                    · linarith only [h0, h4, h754, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h756 | h756
                      · linarith only [h0, h397, h756, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h758 | h758
                        · linarith only [h0, h567, h758, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h760 | h760
                          · linarith only [h1, h4, h613, h760, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h762 | h762
                            · linarith only [h1, h720, h762, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h764 | h764
                              · linarith only [h2, h738, h764, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h766 | h766
                                · linarith only [h0, h4, h613, h766, hc12, hlam, hphi, ht23, u3elo2]
                                · linarith only [h0, h4, h766, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h769 | h769
        · rcases m.htr 0 2 4 (by decide) (by decide) with h770 | h770
          · rcases m.htr 0 2 5 (by decide) (by decide) with h771 | h771
            · linarith only [h0, h3, h771, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h773 | h773
              · rcases m.htr 0 3 5 (by decide) (by decide) with h774 | h774
                · linarith only [h1, h3, h774, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h776 | h776
                  · linarith only [h2, h3, h776, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h778 | h778
                    · linarith only [h0, h3, h774, h778, hc23, hlam, hphi, u3elo4]
                    · linarith only [h769, h771, h778, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h781 | h781
                · linarith only [h0, h3, h773, h781, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h783 | h783
                  · linarith only [h0, h3, h770, h783, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h785 | h785
                    · linarith only [h0, h3, h781, h785, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h3, h769, h781, h785, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h788 | h788
            · linarith only [h2, h3, h770, h788, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h790 | h790
              · linarith only [h769, h770, h790, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h792 | h792
                · linarith only [h2, h3, h769, h770, h792, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h794 | h794
                  · linarith only [h2, h3, h794, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h796 | h796
                    · linarith only [h0, h3, h792, h796, hc23, hlam, hphi, u3elo4]
                    · linarith only [h769, h788, h796, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h799 | h799
          · rcases m.htr 0 2 5 (by decide) (by decide) with h800 | h800
            · linarith only [h0, h3, h800, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h802 | h802
              · rcases m.htr 0 3 5 (by decide) (by decide) with h803 | h803
                · linarith only [h1, h3, h803, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h805 | h805
                  · linarith only [h0, h3, h769, h799, h803, h805, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h807 | h807
                    · linarith only [h0, h769, h803, h807, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h809 | h809
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h810 | h810
                        · linarith only [h1, h3, h800, h807, h810, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h812 | h812
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h813 | h813
                            · linarith only [h1, h3, h803, h813, hlam]
                            · linarith only [h1, h3, h807, h809, h813, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h802, h807, h809, h812, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h769, h799, h803, h809, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h769, h799, h802, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h819 | h819
            · linarith only [h0, h3, h819, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h821 | h821
              · rcases m.htr 0 3 5 (by decide) (by decide) with h822 | h822
                · linarith only [h1, h3, h822, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h824 | h824
                  · linarith only [h1, h3, h821, h822, h824, hc13, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h826 | h826
                    · linarith only [h0, h799, h821, h822, h826, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h828 | h828
                      · linarith only [h799, h826, h828, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h830 | h830
                        · linarith only [h0, h3, h769, h819, h830, hc01, hlam, hphi, ht12, ht23, u3elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h832 | h832
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h833 | h833
                            · linarith only [h1, h3, h822, h833, hlam]
                            · linarith only [h1, h3, h832, h833, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h821, h826, h832, hc12, hlam, hphi, ht23, u3elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h837 | h837
                · linarith only [h0, h3, h821, h837, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h839 | h839
                  · linarith only [h2, h3, h839, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h841 | h841
                    · linarith only [h0, h769, h841, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h843 | h843
                      · linarith only [h1, h3, h799, h837, h841, h843, hc02, hlam, hphi, ht23, u3elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h845 | h845
                        · linarith only [h0, h819, h845, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h847 | h847
                          · linarith only [h1, h3, h821, h837, h847, hc03, hlam, hphi, u3elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h849 | h849
                            · linarith only [h0, h3, h837, h849, hc12, hlam, hphi, ht23, u3elo1]
                            · linarith only [h2, h3, h841, h847, h849, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h852 | h852
      · rcases m.htr 0 2 3 (by decide) (by decide) with h853 | h853
        · rcases m.htr 0 2 4 (by decide) (by decide) with h854 | h854
          · linarith only [h0, h2, h854, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h856 | h856
            · rcases m.htr 0 3 4 (by decide) (by decide) with h857 | h857
              · linarith only [h1, h2, h857, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h859 | h859
                · rcases m.htr 0 4 5 (by decide) (by decide) with h860 | h860
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h861 | h861
                    · linarith only [h0, h2, h857, h861, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h2, h853, h857, h861, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h0, h2, h853, h857, h859, h860, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h865 | h865
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h866 | h866
                    · linarith only [h0, h2, h857, h866, hc23, hlam, hphi, u3elo3]
                    · linarith only [h853, h854, h866, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2, h856, h865, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h870 | h870
              · linarith only [h1, h2, h870, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h872 | h872
                · linarith only [h853, h856, h870, h872, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h874 | h874
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h875 | h875
                    · linarith only [h0, h2, h870, h875, hc23, hlam, hphi, u3elo3]
                    · linarith only [h853, h856, h875, hc12, hc25, hlam, hphi]
                  · linarith only [h2, h852, h874, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h879 | h879
          · linarith only [h0, h2, h879, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h881 | h881
            · rcases m.htr 0 3 4 (by decide) (by decide) with h882 | h882
              · linarith only [h1, h2, h882, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h884 | h884
                · rcases m.htr 0 4 5 (by decide) (by decide) with h885 | h885
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h886 | h886
                    · linarith only [h0, h853, h882, h886, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h888 | h888
                      · linarith only [h1, h2, h879, h886, h888, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h890 | h890
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h891 | h891
                          · linarith only [h1, h2, h882, h891, hlam]
                          · linarith only [h1, h2, h886, h891, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h853, h881, h882, h890, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1, h2, h853, h881, h882, h885, hc13, hlam, hphi, u3elo3]
                · linarith only [h853, h881, h884, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h897 | h897
              · linarith only [h1, h2, h897, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h899 | h899
                · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h901 | h901
                    · linarith only [h0, h881, h897, h899, h901, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h903 | h903
                      · linarith only [h1, h2, h879, h901, h903, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h905 | h905
                        · linarith only [h0, h881, h905, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h907 | h907
                          · linarith only [h1, h881, h897, h899, h907, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h2, h907, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h2, h852, h900, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h911 | h911
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h912 | h912
                    · linarith only [h0, h853, h912, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h914 | h914
                      · linarith only [h0, h879, h914, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h916 | h916
                        · linarith only [h0, h881, h916, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h918 | h918
                          · linarith only [h1, h2, h897, h918, hlam]
                          · linarith only [h1, h2, h912, h918, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h2, h852, h911, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h922 | h922
        · rcases m.htr 0 2 4 (by decide) (by decide) with h923 | h923
          · linarith only [h0, h2, h923, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h925 | h925
            · linarith only [h0, h852, h925, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h927 | h927
              · linarith only [h1, h2, h927, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h929 | h929
                · linarith only [h0, h852, h922, h929, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h931 | h931
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h932 | h932
                    · linarith only [h0, h852, h927, h931, h932, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h852, h922, h927, h931, h932, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h935 | h935
                    · linarith only [h0, h2, h929, h931, h935, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h2, h922, h929, h931, h935, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h938 | h938
          · linarith only [h0, h2, h938, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h940 | h940
            · linarith only [h0, h852, h922, h940, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h942 | h942
              · linarith only [h1, h2, h942, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h944 | h944
                · linarith only [h0, h852, h942, h944, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h946 | h946
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h947 | h947
                    · linarith only [h0, h922, h942, h947, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h949 | h949
                      · linarith only [h0, h852, h938, h946, h949, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h951 | h951
                        · linarith only [h1, h852, h940, h947, h951, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h953 | h953
                          · linarith only [h1, h852, h942, h946, h953, hlam]
                          · linarith only [h1, h2, h947, h953, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h956 | h956
                    · linarith only [h0, h922, h956, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h958 | h958
                      · linarith only [h0, h2, h946, h958, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h960 | h960
                        · linarith only [h1, h2, h940, h946, h956, h960, hc02, hc45, hlam, hphi, ht23, ht34]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h962 | h962
                          · linarith only [h1, h2, h946, h962, hc34, hc45, hlam, hphi]
                          · linarith only [h1, h2, h962, hc13, hlam, hphi, u3elo3]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
