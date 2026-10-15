import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_M_LI_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h10, h13, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h12, h4, h5, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                        · linarith only [h0, h10, h11, h4, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h4, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h20, h8, h9, hlam]
                        · linarith only [h0, h19, h20, h4, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                      · linarith only [h0, h19, h4, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                  · linarith only [h0, h4, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                          · linarith only [h0, h25, h27, h29, h7, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                            · linarith only [h0, h25, h31, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1, h27, h31, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h27, h28, h4, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h27, h4, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                        · linarith only [h25, h26, h37, hlam]
                        · linarith only [h0, h36, h37, h4, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                      · linarith only [h0, h36, h4, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                  · linarith only [h0, h25, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
                · linarith only [h42, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
                        · linarith only [h2, h44, h47, h5, h6, hc12, hlam, hphi, u1ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                          · linarith only [h2, h42, h49, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                            · linarith only [h0, h44, h51, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h5, h51, h6, hc23, hc35, hlam, hphi]
                      · linarith only [h46, h5, h6, hc13, hc35, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                        · linarith only [h1, h56, h6, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                          · linarith only [h2, h42, h58, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                            · linarith only [h3, h44, h45, h60, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h5, h6, h60, hc23, hc35, hlam, hphi]
                      · linarith only [h5, h55, h6, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h4, h44, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h65 | h65
              · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
                · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h69 | h69
                      · linarith only [h0, h5, h65, h67, h69, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                            · linarith only [h0, h3, h5, h65, h67, h73, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                              · linarith only [h0, h67, h75, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h5, h65, h75, hc23, hc34, hlam, hphi]
                          · linarith only [h66, h69, h71, h72, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h5, h65, h71, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                      · linarith only [h5, h65, h67, h68, h80, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h82 | h82
                        · linarith only [h67, h68, h82, hlam]
                        · linarith only [h65, h82, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi2]
                  · linarith only [h0, h4, h67, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · linarith only [h5, h65, h66, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h87 | h87
                · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                      · linarith only [h0, h5, h88, h90, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                        · linarith only [h1, h65, h92, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                            · linarith only [h0, h5, h88, h95, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                              · linarith only [h0, h1, h65, h88, h97, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                                · rcases h3bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u0elo2, u1ehi2]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h65, h99, hc23, hc34, hlam, hphi, p100_1]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h5, hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h65, hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h1, hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h90, hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h92, hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h4, hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h88, hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h95, hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h97, hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht12, ht23, p100_1, u1ehi2]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [hc34, hlam, hphi, ht12, ht23, p100_1, u1ehi2]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    rcases p100_3 (m.d 0 3) (by simp) with h118 | h118
                                    · linarith only [h118, h5, hlam]
                                    · linarith only [h118, h4, hlam]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h1, h65, hc34, hlam, hphi, ht12, ht23, p100_1, u1ehi2]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h1, hc35, hlam, hphi, ht12, ht23, p100_1, u1ehi2]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht12, ht23, p100_1, u1ehi2]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    rcases p100_3 (m.d 0 3) (by simp) with h125 | h125
                                    · linarith only [h125, h65, hlam]
                                    · linarith only [h125, h4, hlam]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [h99, hlam, p100_0]
                                  · have p100_0 := h100c.1
                                    have p100_1 := h100c.2.1
                                    have p100_2 := h100c.2.2.1
                                    have p100_3 := h100c.2.2.2
                                    linarith only [hlam, p100_0]
                                · linarith only [h1, h5, h99, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                          · linarith only [h2, h87, h94, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                      · linarith only [h1, h132, h5, h87, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                        · linarith only [h134, h3, h65, h88, h89, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                            · linarith only [h1, h137, h5, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                              · linarith only [h1, h136, h139, h2, h65, h88, h89, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                                · rcases h3bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p142_1, u0elo2, u1ehi2]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h5, hc23, hc34, hlam, hphi, p142_1]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h5, hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h65, hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h1, hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u0elo0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h132, hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h134, hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h4, hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h88, hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h137, hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h139, hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht12, ht23, p142_1, u1ehi2]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [hc34, hlam, hphi, ht12, ht23, p142_1, u1ehi2]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    rcases p142_3 (m.d 0 3) (by simp) with h160 | h160
                                    · linarith only [h160, h5, hlam]
                                    · linarith only [h160, h4, hlam]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h139, h89, hc12, hc34, hlam, hphi, ht23, p142_1]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h1, hc35, hlam, hphi, ht12, ht23, p142_1, u1ehi2]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht12, ht23, p142_1, u1ehi2]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    rcases p142_3 (m.d 0 3) (by simp) with h167 | h167
                                    · linarith only [h167, h65, hlam]
                                    · linarith only [h167, h4, hlam]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [h141, hlam, p142_0]
                                  · have p142_0 := h142c.1
                                    have p142_1 := h142c.2.1
                                    have p142_2 := h142c.2.2.1
                                    have p142_3 := h142c.2.2.2
                                    linarith only [hlam, p142_0]
                                · linarith only [h1, h141, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                          · linarith only [h136, h87, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                  · linarith only [h0, h4, h88, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h177 | h177
                      · linarith only [h1, h177, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h179 | h179
                        · linarith only [h1, h179, h65, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h181 | h181
                          · linarith only [h181, h2, h87, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                            · linarith only [h1, h175, h183, h5, hc12, hlam, hphi, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                              · linarith only [h0, h175, h185, h65, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                                · linarith only [h1, h187, h5, h87, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                · linarith only [h1, h187, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h190 | h190
                      · linarith only [h1, h190, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                        · linarith only [h1, h192, h65, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                          · linarith only [h1, h194, h5, h87, hc14, hlam, hphi, u1ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                            · linarith only [h1, h196, h5, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                              · linarith only [h1, h175, h176, h198, h3, h65, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h200 | h200
                                · linarith only [h1, h200, h5, h87, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                · linarith only [h1, h200, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                  · linarith only [h0, h175, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h204 | h204
            · rcases m.htr 0 3 5 (by decide) (by decide) with h205 | h205
              · rcases m.htr 0 4 5 (by decide) (by decide) with h206 | h206
                · rcases m.htr 1 2 3 (by decide) (by decide) with h207 | h207
                  · linarith only [h0, h207, h4, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h210 | h210
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h211 | h211
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h212 | h212
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h213 | h213
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h214 | h214
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h215 | h215
                                · linarith only [h1, h210, h215, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h1, h210, h212, h215, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h0, h209, h214, h4, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                            · linarith only [h0, h209, h213, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                          · linarith only [h206, h212, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                        · linarith only [h205, h207, h209, h211, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h1, h204, h207, h209, h210, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h224 | h224
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h228 | h228
                                · linarith only [h1, h223, h228, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h2, h225, h228, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h1, h224, h227, h4, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h0, h226, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h204, h206, h225, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi3]
                        · linarith only [h205, h223, h224, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1, h204, h207, h223, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h236 | h236
                  · linarith only [h0, h1, h236, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h240 | h240
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h241 | h241
                          · linarith only [h2, h206, h241, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h243 | h243
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h244 | h244
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h245 | h245
                                · linarith only [h1, h2, h206, h239, h245, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi3]
                                · rcases h3bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p247_1, u0elo2, u1ehi2]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h4, hlam, p247_1]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    rcases p247_3 (m.d 0 3) (by simp) with h251 | h251
                                    · rcases p247_3 (m.d 1 3) (by simp) with h252 | h252
                                      · linarith only [h1, h252, hlam]
                                      · linarith only [h239, h252, hlam]
                                    · linarith only [h251, hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    rcases p247_3 (m.d 0 3) (by simp) with h256 | h256
                                    · rcases p247_3 (m.d 1 3) (by simp) with h257 | h257
                                      · linarith only [h1, h257, hlam]
                                      · linarith only [h240, h257, hlam]
                                    · linarith only [h256, hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h1, hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h236, hlam, p247_1]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p247_1, u0elo0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h1, hc35, hlam, hphi, ht0b, ht5b, p247_1, u0elo0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h1, hc23, hlam, hphi, ht12, p247_1, u1ehi2]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht12, p247_1, u1ehi2]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    rcases p247_3 (m.d 0 3) (by simp) with h269 | h269
                                    · linarith only [h269, h4, hlam]
                                    · linarith only [h204, h269, hlam]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    rcases p247_3 (m.d 0 3) (by simp) with h272 | h272
                                    · linarith only [h272, h4, hlam]
                                    · linarith only [h205, h272, hlam]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h204, hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h239, hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h243, hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h245, hlam, p247_1]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h205, hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h240, hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h244, hlam, p247_0]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [h205, hc34, hlam, hphi, ht0b, ht45, ht5b, p247_1, u0elo2]
                                  · have p247_0 := h247c.1
                                    have p247_1 := h247c.2.1
                                    have p247_2 := h247c.2.2.1
                                    have p247_3 := h247c.2.2.2
                                    linarith only [hlam, p247_0]
                              · linarith only [h1, h240, h244, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h0, h243, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h205, h239, h240, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1, h204, h236, h238, h239, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h289 | h289
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h290 | h290
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h291 | h291
                          · linarith only [h2, h206, h291, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h293 | h293
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h294 | h294
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h295 | h295
                                · linarith only [h2, h206, h289, h295, hc13, hlam, hphi, u1ehi3]
                                · rcases h3bigk with h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h1, h290, h295, hc34, hlam, hphi, ht0b, ht45, ht5b, p297_1, u0elo0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h4, hlam, p297_1]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    rcases p297_3 (m.d 0 3) (by simp) with h301 | h301
                                    · rcases p297_3 (m.d 1 3) (by simp) with h302 | h302
                                      · linarith only [h1, h302, hlam]
                                      · linarith only [h289, h302, hlam]
                                    · linarith only [h301, hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    rcases p297_3 (m.d 0 3) (by simp) with h306 | h306
                                    · rcases p297_3 (m.d 1 3) (by simp) with h307 | h307
                                      · linarith only [h1, h307, hlam]
                                      · linarith only [h290, h307, hlam]
                                    · linarith only [h306, hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h1, hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h236, hlam, p297_1]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p297_1, u0elo0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h1, h295, hc34, hlam, hphi, ht0b, ht45, ht5b, p297_1, u0elo0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h1, hc23, hlam, hphi, ht12, p297_1, u1ehi2]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht12, p297_1, u1ehi2]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    rcases p297_3 (m.d 0 3) (by simp) with h319 | h319
                                    · linarith only [h319, h4, hlam]
                                    · linarith only [h204, h319, hlam]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    rcases p297_3 (m.d 0 3) (by simp) with h322 | h322
                                    · linarith only [h322, h4, hlam]
                                    · linarith only [h205, h322, hlam]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h204, hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h289, hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h293, hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h295, hlam, p297_1]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h205, hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h290, hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h294, hlam, p297_0]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [h205, hc34, hlam, hphi, ht0b, ht45, ht5b, p297_1, u0elo2]
                                  · have p297_0 := h297c.1
                                    have p297_1 := h297c.2.1
                                    have p297_2 := h297c.2.2.1
                                    have p297_3 := h297c.2.2.2
                                    linarith only [hlam, p297_0]
                              · linarith only [h1, h290, h294, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h0, h293, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h205, h289, h290, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1, h204, h236, h289, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h339 | h339
                · linarith only [h204, h205, h339, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                  · linarith only [h0, h341, h4, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h343 | h343
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h345 | h345
                        · linarith only [h1, h205, h345, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h341, h343, h345, hlam]
                      · linarith only [h204, h205, h341, h343, h344, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h349 | h349
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h350 | h350
                        · linarith only [h1, h205, h350, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h352 | h352
                          · linarith only [h2, h3, h339, h341, h350, h352, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h354 | h354
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h355 | h355
                              · linarith only [h2, h204, h205, h355, hc23, hlam, hphi, ht12, u1ehi3]
                              · linarith only [h0, h355, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h0, h3, h349, h350, h354, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                      · linarith only [h204, h205, h349, hc13, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h360 | h360
              · rcases m.htr 0 4 5 (by decide) (by decide) with h361 | h361
                · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
                  · linarith only [h0, h362, h4, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h364 | h364
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h365 | h365
                      · linarith only [h1, h204, h365, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h367 | h367
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h368 | h368
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h369 | h369
                            · linarith only [h0, h204, h364, h369, h4, hc23, hlam, hphi, ht12, u1ehi4]
                            · linarith only [h0, h364, h369, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                          · linarith only [h361, h362, h364, h365, h368, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi4]
                        · linarith only [h360, h362, h364, h367, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h374 | h374
                      · linarith only [h1, h204, h360, h374, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h376 | h376
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h377 | h377
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h378 | h378
                            · linarith only [h204, h3, h360, h364, h378, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h0, h378, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h2, h361, h364, h374, h376, h377, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                        · linarith only [h360, h376, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi2]
                · linarith only [h204, h360, h361, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h384 | h384
                · rcases m.htr 1 2 3 (by decide) (by decide) with h385 | h385
                  · linarith only [h0, h385, h4, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
                      · linarith only [h1, h204, h388, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h390 | h390
                        · linarith only [h1, h3, h360, h390, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
                        · linarith only [h385, h387, h390, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h393 | h393
                      · linarith only [h1, h204, h393, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h395 | h395
                        · linarith only [h1, h360, h395, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h397 | h397
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h398 | h398
                            · linarith only [h0, h204, h398, h4, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h0, h398, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h2, h384, h397, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h402 | h402
                  · linarith only [h0, h4, h402, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h405 | h405
                      · linarith only [h1, h204, h405, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
                        · linarith only [h1, h360, h407, hlam]
                        · linarith only [h402, h404, h407, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h410 | h410
                      · linarith only [h0, h204, h4, h410, hc13, hlam, hphi, u1ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h412 | h412
                        · linarith only [h1, h360, h412, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h414 | h414
                          · linarith only [h0, h204, h384, h4, h414, hc14, hlam, hphi, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h416 | h416
                            · linarith only [h0, h204, h4, h416, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h0, h4, h416, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h422 | h422
    · linarith only [h0, h422, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h424 | h424
      · linarith only [h0, h424, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h426 | h426
        · linarith only [h0, h426, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h428 | h428
          · rcases m.htr 0 3 4 (by decide) (by decide) with h429 | h429
            · rcases m.htr 0 3 5 (by decide) (by decide) with h430 | h430
              · rcases m.htr 0 4 5 (by decide) (by decide) with h431 | h431
                · rcases m.htr 1 2 3 (by decide) (by decide) with h432 | h432
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h433 | h433
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h434 | h434
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h435 | h435
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h436 | h436
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h437 | h437
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h438 | h438
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h439 | h439
                                · linarith only [h428, h437, h439, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                · rcases h3bigk with h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h422, hlam, p441_1]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h428, h438, hc35, hlam, hphi, ht0b, ht5b, p441_1, u0elo1]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    rcases p441_3 (m.d 0 3) (by simp) with h445 | h445
                                    · rcases p441_3 (m.d 1 3) (by simp) with h446 | h446
                                      · rcases p441_3 (m.d 2 3) (by simp) with h447 | h447
                                        · linarith only [h428, h447, hlam]
                                        · linarith only [h437, h447, hlam]
                                      · linarith only [h434, h446, hlam]
                                    · linarith only [h445, hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    rcases p441_3 (m.d 0 3) (by simp) with h452 | h452
                                    · rcases p441_3 (m.d 1 3) (by simp) with h453 | h453
                                      · rcases p441_3 (m.d 2 3) (by simp) with h454 | h454
                                        · linarith only [h428, h454, hlam]
                                        · linarith only [h438, h454, hlam]
                                      · linarith only [h435, h453, hlam]
                                    · linarith only [h452, hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h422, h432, hc12, hlam, hphi, p441_1, u1ehi0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    rcases p441_3 (m.d 0 3) (by simp) with h461 | h461
                                    · linarith only [h422, h461, hlam]
                                    · linarith only [h428, h461, hlam]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    rcases p441_3 (m.d 0 3) (by simp) with h464 | h464
                                    · linarith only [h422, h464, hlam]
                                    · linarith only [h429, h464, hlam]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    rcases p441_3 (m.d 0 3) (by simp) with h467 | h467
                                    · linarith only [h422, h467, hlam]
                                    · linarith only [h430, h467, hlam]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h428, hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h432, hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h428, hc34, hlam, hphi, ht0b, ht45, ht5b, p441_1, u0elo1]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h428, h439, hc34, hlam, hphi, ht0b, ht45, ht5b, p441_1, u0elo1]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h429, hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h434, hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h437, hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h439, hlam, p441_1]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h430, hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h435, hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h438, hlam, p441_0]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [h430, hc34, hlam, hphi, ht0b, ht45, ht5b, p441_1, u0elo2]
                                  · have p441_0 := h441c.1
                                    have p441_1 := h441c.2.1
                                    have p441_2 := h441c.2.2.1
                                    have p441_3 := h441c.2.2.2
                                    linarith only [hlam, p441_0]
                              · linarith only [h428, h430, h437, h438, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h486 | h486
                              · linarith only [h428, h429, h437, h486, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h488 | h488
                                · rcases h3bigk with h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h422, hlam, p489_1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    rcases p489_3 (m.d 0 3) (by simp) with h492 | h492
                                    · rcases p489_3 (m.d 1 3) (by simp) with h493 | h493
                                      · rcases p489_3 (m.d 2 3) (by simp) with h494 | h494
                                        · linarith only [h428, h494, hlam]
                                        · rcases p489_3 (m.d 3 4) (by simp) with h496 | h496
                                          · linarith only [h429, h496, hlam]
                                          · linarith only [h437, h496, hlam]
                                      · linarith only [h432, h493, hlam]
                                    · linarith only [h428, h492, hlam]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h428, h486, h488, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1, u0elo1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h428, h486, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1, u0elo1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h422, h432, hc12, hlam, hphi, p489_1, u1ehi0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    rcases p489_3 (m.d 0 3) (by simp) with h505 | h505
                                    · linarith only [h422, h505, hlam]
                                    · linarith only [h428, h505, hlam]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    rcases p489_3 (m.d 0 3) (by simp) with h508 | h508
                                    · linarith only [h422, h508, hlam]
                                    · linarith only [h429, h508, hlam]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    rcases p489_3 (m.d 0 3) (by simp) with h511 | h511
                                    · linarith only [h422, h511, hlam]
                                    · linarith only [h430, h511, hlam]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h428, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h432, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h437, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h486, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h429, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h434, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h429, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1, u0elo2]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h428, h429, h486, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1, u0elo1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h430, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h435, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h428, h430, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1, u0elo1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h488, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [hlam, p489_0]
                                · linarith only [h428, h429, h431, h437, h488, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h428, h429, h431, h436, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi3]
                        · linarith only [h428, h430, h435, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi2]
                      · linarith only [h422, h434, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h433, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h432, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h536 | h536
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h537 | h537
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h538 | h538
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h539 | h539
                          · linarith only [h424, h431, h535, h537, h539, hc12, hlam, hphi, u1ehi0]
                          · linarith only [h424, h539, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                        · linarith only [h422, h430, h538, hlam]
                      · linarith only [h422, h429, h537, hlam]
                    · linarith only [h0, h536, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h428, h535, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h546 | h546
                · linarith only [h429, h430, h546, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h548 | h548
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h549 | h549
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h550 | h550
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h551 | h551
                        · linarith only [h424, h429, h430, h551, hc13, hlam, hphi, u1ehi0]
                        · linarith only [h422, h551, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h422, h429, h550, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi0]
                    · linarith only [h0, h549, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h428, h548, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h557 | h557
              · rcases m.htr 0 4 5 (by decide) (by decide) with h558 | h558
                · rcases m.htr 1 2 3 (by decide) (by decide) with h559 | h559
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h560 | h560
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h561 | h561
                      · linarith only [h426, h429, h557, h561, hc13, hlam, hphi, u1ehi0]
                      · linarith only [h422, h561, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h560, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h428, h559, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                · linarith only [h429, h557, h558, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h567 | h567
                · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h570 | h570
                      · linarith only [h422, h429, h570, hc13, hlam, hphi, u1ehi0]
                      · linarith only [h422, h570, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h569, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h428, h568, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h575 | h575
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h576 | h576
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h577 | h577
                      · linarith only [h422, h429, h577, hc13, hlam, hphi, u1ehi0]
                      · linarith only [h422, h577, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h576, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h428, h575, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h582 | h582
            · rcases m.htr 0 3 5 (by decide) (by decide) with h583 | h583
              · rcases m.htr 0 4 5 (by decide) (by decide) with h584 | h584
                · rcases m.htr 1 2 3 (by decide) (by decide) with h585 | h585
                  · linarith only [h0, h428, h585, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h585, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                  · linarith only [h0, h428, h588, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h588, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h591 | h591
                · linarith only [h582, h583, h591, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h593 | h593
                  · linarith only [h0, h428, h593, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h593, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h596 | h596
              · rcases m.htr 0 4 5 (by decide) (by decide) with h597 | h597
                · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                  · linarith only [h0, h428, h598, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h598, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h582, h596, h597, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h602 | h602
                · rcases m.htr 1 2 3 (by decide) (by decide) with h603 | h603
                  · linarith only [h0, h428, h603, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h603, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                  · linarith only [h0, h428, h606, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h606, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_20_11_14_M_LR_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1ehi := hb1.1
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
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h0, h11, h14, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h0, h13, h4, h6, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                          · linarith only [h0, h11, h12, h4, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h11, h4, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h10, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · linarith only [h0, h4, h9, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                            · linarith only [h22, h24, h26, h8, hc12, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                              · linarith only [h0, h22, h28, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h0, h22, h24, h28, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h24, h25, h4, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h24, h4, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h23, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · linarith only [h0, h22, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h35, h6, h7, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h39 | h39
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
                          · linarith only [h37, h40, h6, h7, hc12, hlam, hphi, ht01, u0ehi8]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                            · linarith only [h0, h35, h37, h39, h42, hlam, hphi, u0ehi8, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                              · linarith only [h0, h37, h44, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h44, h6, h7, hc23, hc35, hlam, hphi]
                        · linarith only [h39, h6, h7, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h38, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · linarith only [h0, h37, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h50 | h50
                · rcases m.htr 0 4 5 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                        · linarith only [h52, h54, h6, hc12, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                              · linarith only [h0, h50, h52, h58, h6, hlam, hphi, u0ehi9, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                                · linarith only [h0, h53, h58, h60, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h50, h6, h60, hc23, hc34, hlam, hphi]
                            · linarith only [h51, h54, h56, h57, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h50, h56, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi2]
                      · linarith only [h0, h5, h53, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · linarith only [h0, h4, h52, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · linarith only [h50, h51, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h68 | h68
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                        · linarith only [h6, h71, hc13, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
                          · linarith only [h50, h73, hc13, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                              · linarith only [h0, h6, h69, h76, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h78 | h78
                                · linarith only [h0, h50, h70, h76, h78, hlam, hphi, u0ehi7, u0elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h80 | h80
                                  · linarith only [h0, h70, h80, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h0, h70, h75, h76, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h0, h5, h68, h75, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                      · linarith only [h0, h5, h70, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · linarith only [h0, h4, h69, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                        · linarith only [h6, h86, h88, hc12, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
                          · linarith only [h0, h50, h87, h88, h90, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                            · linarith only [h0, h68, h87, h92, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                              · linarith only [h0, h6, h86, h94, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                                · linarith only [h0, h50, h87, h94, h96, hlam, hphi, u0ehi7, u0elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                                  · linarith only [h0, h6, h68, h87, h98, hlam, hphi, u0ehi7, u0elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
                                    · linarith only [h0, h100, h6, h68, h87, h88, hc34, hlam, hphi, ht12, ht23, u0ehi7, u0elo0, u1ehi2]
                                    · linarith only [h0, h100, h6, h87, h88, hc45, hlam, hphi, ht12, ht23, ht34, u0ehi7, u0elo0, u1ehi2]
                      · linarith only [h0, h5, h87, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · linarith only [h0, h4, h86, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h105 | h105
              · linarith only [h105, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h107 | h107
                · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                      · linarith only [h110, h5, hc12, hlam, hphi, ht01, u0ehi6]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                        · linarith only [h105, h109, h110, h112, h2, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                              · linarith only [h105, h107, h109, h110, h116, h2, hlam, hphi, u0ehi9, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                                · linarith only [h109, h110, h118, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h107, h116, h118, h4, h5, hc23, hc34, hlam, hphi]
                            · linarith only [h108, h109, h110, h114, h115, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi4]
                          · linarith only [h107, h114, h4, h5, hc24, hlam, hphi, ht12, u1ehi2]
                    · linarith only [h109, h4, h5, hc24, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h107, h108, h4, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                      · linarith only [h0, h127, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                        · linarith only [h105, h126, h127, h129, h2, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h131 | h131
                          · linarith only [h107, h126, h127, h131, h2, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h133 | h133
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                              · linarith only [h105, h126, h127, h134, h2, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                                · linarith only [h107, h126, h127, h136, h2, hlam, hphi, u0ehi7, u0elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h138 | h138
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h139 | h139
                                    · rcases h4bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h126, h127, h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p140_1, u0elo0, u1ehi2]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h5, hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h105, hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        rcases p140_3 (m.d 0 4) (by simp) with h145 | h145
                                        · rcases p140_3 (m.d 1 4) (by simp) with h146 | h146
                                          · linarith only [h146, h2, hlam]
                                          · linarith only [h133, h146, hlam]
                                        · linarith only [h145, hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h2, hlam, p140_1]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h127, hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h129, hlam, p140_1]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p140_1, u0elo0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [hc24, hlam, hphi, ht01, ht12, p140_1, u0ehi8]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h134, hc34, hlam, hphi, ht12, ht23, p140_1, u1ehi3]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h134, hlam, p140_1]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        rcases p140_3 (m.d 0 4) (by simp) with h159 | h159
                                        · linarith only [h159, h5, hlam]
                                        · linarith only [h125, h159, hlam]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h126, h127, h2, h4, h5, hc34, hlam, hphi, ht12, ht23, p140_1, u0ehi7, u0elo0, u1ehi2]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h126, h127, hc34, hlam, hphi, ht12, ht23, p140_1, u1ehi2]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h126, h127, h2, h4, h5, hc34, hlam, hphi, ht12, ht23, p140_1, u0ehi7, u0elo0, u1ehi2]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        rcases p140_3 (m.d 0 4) (by simp) with h166 | h166
                                        · linarith only [h105, h166, hlam]
                                        · linarith only [h125, h166, hlam]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h125, hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h133, hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h138, hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [h139, hlam, p140_0]
                                      · have p140_0 := h140c.1
                                        have p140_1 := h140c.2.1
                                        have p140_2 := h140c.2.2.1
                                        have p140_3 := h140c.2.2.2
                                        linarith only [hlam, p140_0]
                                    · linarith only [h126, h127, h134, h139, h2, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u0ehi7, u0elo0, u1ehi2]
                                  · linarith only [h133, h138, h2, h4, h5, hlam, hphi, u0ehi7, u0elo0]
                            · linarith only [h125, h126, h127, h133, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi2]
                    · linarith only [h126, h4, h5, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h179 | h179
                      · linarith only [h179, h4, h5, hc12, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                        · linarith only [h105, h178, h179, h181, h2, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                          · linarith only [h107, h178, h179, h183, h2, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h185 | h185
                            · linarith only [h125, h185, h2, h4, h5, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                              · linarith only [h105, h178, h179, h185, h187, h3, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h189 | h189
                                · linarith only [h107, h178, h179, h185, h189, h3, hlam, hphi, u0ehi7, u0elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h191 | h191
                                  · linarith only [h125, h178, h179, h185, h191, h3, h4, h5, hc24, hlam, hphi, ht12, u0ehi7, u0elo0, u1ehi2]
                                  · linarith only [h178, h179, h185, h191, h3, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u0ehi7, u0elo0, u1ehi2]
                    · linarith only [h178, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h195 | h195
            · rcases m.htr 0 3 4 (by decide) (by decide) with h196 | h196
              · rcases m.htr 0 3 5 (by decide) (by decide) with h197 | h197
                · rcases m.htr 0 4 5 (by decide) (by decide) with h198 | h198
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
                    · linarith only [h195, h198, h199, h4, hc12, hlam, hphi, ht01, u0ehi9]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h203 | h203
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h204 | h204
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h206 | h206
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                                  · linarith only [h1, h199, h201, h207, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h1, h199, h201, h204, h205, h207, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h1, h195, h198, h203, h206, h4, hlam, hphi, u0ehi9, u0elo0]
                              · linarith only [h1, h195, h198, h199, h201, h204, h205, h4, hc34, hlam, hphi, ht12, ht23, u0ehi9, u0elo0, u1ehi4]
                            · linarith only [h195, h198, h204, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi3]
                          · linarith only [h1, h197, h199, h201, h203, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                        · linarith only [h1, h196, h199, h201, h202, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                      · linarith only [h195, h201, h4, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
                    · linarith only [h216, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h221 | h221
                            · linarith only [h1, h198, h216, h218, h221, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h224 | h224
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h225 | h225
                                  · linarith only [h1, h198, h216, h218, h225, hc24, hlam, hphi, ht12, u0ehi8, u0elo0, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h227 | h227
                                    · linarith only [h1, h198, h216, h218, h223, h227, hlam, hphi, u0ehi8, u0elo0]
                                    · rcases h4bigk with h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [hlam, p229_0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h198, hc14, hc45, hlam, hphi, p229_1]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h198, hc24, hc45, hlam, hphi, p229_1]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h198, hc34, hc45, hlam, hphi, p229_1]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h198, hlam, p229_0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h2, hlam, p229_1]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [hlam, p229_0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h2, h223, hc34, hlam, hphi, ht0b, ht45, ht5b, p229_1, u0elo0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h1, h216, h218, hc34, hlam, hphi, ht0b, ht45, ht5b, p229_1, u0elo0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h221, hlam, p229_0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h195, hlam, p229_1]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h218, hlam, p229_1]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [hlam, p229_0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h195, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p229_1]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h225, hlam, p229_0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h196, hlam, p229_1]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h219, hlam, p229_0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h223, hlam, p229_0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [hlam, p229_0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [h227, hlam, p229_0]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p229_1, u0ehi8]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p229_1, u1ehi3]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        rcases p229_3 (m.d 0 4) (by simp) with h252 | h252
                                        · linarith only [h198, h252, hlam]
                                        · linarith only [h195, h252, hlam]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        rcases p229_3 (m.d 0 4) (by simp) with h255 | h255
                                        · linarith only [h198, h255, hlam]
                                        · linarith only [h196, h255, hlam]
                                      · have p229_0 := h229c.1
                                        have p229_1 := h229c.2.1
                                        have p229_2 := h229c.2.2.1
                                        have p229_3 := h229c.2.2.2
                                        linarith only [hlam, p229_0]
                                · linarith only [h1, h220, h224, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h1, h195, h216, h218, h223, h4, hc34, hlam, hphi, ht12, ht23, u0ehi8, u0elo0, u1ehi3]
                          · linarith only [h1, h197, h216, h218, h220, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                        · linarith only [h1, h196, h216, h218, h219, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                      · linarith only [h195, h218, h4, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h264 | h264
                  · linarith only [h195, h197, h264, h4, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
                    · linarith only [h266, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h268 | h268
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h269 | h269
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h270 | h270
                          · linarith only [h1, h197, h270, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
                            · linarith only [h264, h266, h268, h270, h272, h3, hlam, hphi, u0ehi8, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                                · linarith only [h195, h197, h266, h268, h270, h275, h3, h4, hc23, hlam, hphi, ht12, u0ehi8, u0elo0, u1ehi3]
                                · linarith only [h195, h266, h268, h270, h275, h3, h4, hc35, hlam, hphi, ht12, ht23, u0ehi8, u0elo0, u1ehi3]
                              · linarith only [h195, h266, h268, h270, h274, h3, h4, hc34, hlam, hphi, ht12, ht23, u0ehi8, u0elo0, u1ehi3]
                        · linarith only [h196, h266, h268, h269, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi3]
                      · linarith only [h195, h268, h4, hc12, hc23, hlam, hphi]
              · linarith only [h195, h196, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h282 | h282
              · rcases m.htr 0 3 5 (by decide) (by decide) with h283 | h283
                · rcases m.htr 0 4 5 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
                    · linarith only [h285, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h287 | h287
                      · linarith only [h1, h195, h285, h287, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h289 | h289
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h290 | h290
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h291 | h291
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h292 | h292
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h293 | h293
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h294 | h294
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h295 | h295
                                    · linarith only [h1, h289, h295, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h1, h289, h291, h295, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h1, h195, h289, h291, h294, hlam, hphi, u0ehi6, u0elo0]
                                · linarith only [h1, h195, h290, h292, h293, hlam, hphi, u0ehi6, u0elo0]
                              · linarith only [h1, h287, h289, h292, h4, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
                            · linarith only [h282, h284, h287, h291, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi1]
                          · linarith only [h1, h283, h287, h289, h290, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                        · linarith only [h1, h282, h289, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h304 | h304
                    · linarith only [h304, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h306 | h306
                      · linarith only [h1, h195, h304, h306, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h308 | h308
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h309 | h309
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h310 | h310
                            · linarith only [h1, h284, h308, h310, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h312 | h312
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h313 | h313
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h314 | h314
                                  · linarith only [h1, h195, h284, h306, h309, h310, h312, h314, hc23, hlam, hphi, ht12, u0ehi6, u0elo0, u1ehi1]
                                  · linarith only [h1, h195, h306, h309, h310, h314, hc45, hlam, hphi, ht12, ht23, ht34, u0ehi6, u0elo0, u1ehi1]
                                · linarith only [h1, h309, h313, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h1, h308, h312, h4, hlam, hphi, u0ehi6, u0elo0]
                          · linarith only [h1, h283, h308, h309, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h282, h304, h308, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h321 | h321
                  · linarith only [h282, h283, h321, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h323 | h323
                    · linarith only [h323, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h325 | h325
                      · linarith only [h195, h325, hc12, hlam, hphi, ht01, u0ehi6]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h327 | h327
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h328 | h328
                          · linarith only [h1, h195, h282, h283, h328, hlam, hphi, u0ehi6, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h330 | h330
                            · linarith only [h195, h3, h321, h327, h328, h330, hlam, hphi, u0ehi6, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h332 | h332
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h333 | h333
                                · linarith only [h195, h282, h283, h3, h325, h327, h328, h333, hc23, hlam, hphi, ht12, u0ehi6, u0elo0, u1ehi1]
                                · linarith only [h3, h325, h327, h328, h333, h4, hc35, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
                              · linarith only [h3, h327, h328, h332, h4, hlam, hphi, u0ehi6, u0elo0]
                        · linarith only [h282, h327, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h338 | h338
                · rcases m.htr 0 4 5 (by decide) (by decide) with h339 | h339
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
                    · linarith only [h340, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
                      · linarith only [h1, h195, h340, h342, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                        · linarith only [h1, h282, h344, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h348 | h348
                              · linarith only [h282, h338, h348, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                              · linarith only [h2, h340, h344, h348, h4, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
                            · linarith only [h339, h340, h344, h347, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi1]
                          · linarith only [h282, h338, h340, h346, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h282, h338, h339, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h354 | h354
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h355 | h355
                    · linarith only [h355, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h357 | h357
                      · linarith only [h195, h357, hc12, hlam, hphi, ht01, u0ehi6]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h359 | h359
                        · linarith only [h1, h282, h359, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                          · linarith only [h2, h338, h359, h361, h4, hlam, hphi, u0ehi6, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                              · linarith only [h2, h282, h355, h361, h363, h364, h4, hc23, hlam, hphi, ht12, u0ehi6, u0elo0, u1ehi1]
                              · linarith only [h2, h355, h361, h363, h364, h4, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
                            · linarith only [h354, h363, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h368 | h368
                    · linarith only [h0, h368, h4, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h370 | h370
                      · linarith only [h1, h195, h368, h370, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                        · linarith only [h1, h282, h372, h4, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                          · linarith only [h2, h338, h372, h374, h4, hlam, hphi, u0ehi6, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h376 | h376
                            · linarith only [h2, h282, h354, h376, h4, hlam, hphi, u0ehi6, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h378 | h378
                              · linarith only [h282, h378, h4, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                              · linarith only [h3, h368, h372, h376, h378, h4, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h384 | h384
    · linarith only [h0, h384, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h386 | h386
      · linarith only [h0, h386, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h388 | h388
        · linarith only [h0, h388, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h390 | h390
          · rcases m.htr 0 2 4 (by decide) (by decide) with h391 | h391
            · rcases m.htr 0 3 4 (by decide) (by decide) with h392 | h392
              · rcases m.htr 0 3 5 (by decide) (by decide) with h393 | h393
                · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h395 | h395
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h396 | h396
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h397 | h397
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h398 | h398
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h400 | h400
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h401 | h401
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h402 | h402
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h403 | h403
                                    · linarith only [h390, h400, h403, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h390, h400, h402, h403, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h406 | h406
                                    · linarith only [h390, h392, h402, h406, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases h4bigk with h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h386, hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        rcases p408_3 (m.d 0 4) (by simp) with h411 | h411
                                        · rcases p408_3 (m.d 1 4) (by simp) with h412 | h412
                                          · rcases p408_3 (m.d 2 4) (by simp) with h413 | h413
                                            · linarith only [h391, h413, hlam]
                                            · rcases p408_3 (m.d 3 4) (by simp) with h415 | h415
                                              · linarith only [h392, h415, hlam]
                                              · rcases p408_3 (m.d 4 5) (by simp) with h417 | h417
                                                · linarith only [h394, h417, hlam]
                                                · linarith only [h402, h417, hlam]
                                          · linarith only [h396, h412, hlam]
                                        · linarith only [h391, h411, hlam]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        rcases p408_3 (m.d 0 4) (by simp) with h422 | h422
                                        · rcases p408_3 (m.d 1 4) (by simp) with h423 | h423
                                          · rcases p408_3 (m.d 2 4) (by simp) with h424 | h424
                                            · linarith only [h391, h424, hlam]
                                            · linarith only [h400, h424, hlam]
                                          · linarith only [h397, h423, hlam]
                                        · linarith only [h392, h422, hlam]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h390, h392, h400, h402, hc34, hlam, hphi, ht0b, ht45, ht5b, p408_1, u0elo1]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h388, h394, h395, h397, hc12, hlam, hphi, p408_1, u1ehi0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        rcases p408_3 (m.d 0 4) (by simp) with h432 | h432
                                        · linarith only [h386, h432, hlam]
                                        · linarith only [h391, h432, hlam]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        rcases p408_3 (m.d 0 4) (by simp) with h435 | h435
                                        · linarith only [h386, h435, hlam]
                                        · linarith only [h392, h435, hlam]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        rcases p408_3 (m.d 0 4) (by simp) with h438 | h438
                                        · linarith only [h386, h438, hlam]
                                        · linarith only [h394, h438, hlam]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h391, hlam, p408_1]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h396, hlam, p408_1]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h390, h392, h394, h402, hc34, hlam, hphi, ht0b, ht45, ht5b, p408_1, u0elo1]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h402, hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h392, hlam, p408_1]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h397, hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h400, hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h406, hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h394, hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h399, hlam, p408_0]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h390, h392, h394, hc24, hlam, hphi, ht0b, ht45, ht5b, p408_1, u0elo1]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [h390, h392, h394, hc34, hlam, hphi, ht0b, ht45, ht5b, p408_1, u0elo1]
                                      · have p408_0 := h408c.1
                                        have p408_1 := h408c.2.1
                                        have p408_2 := h408c.2.2.1
                                        have p408_3 := h408c.2.2.2
                                        linarith only [hlam, p408_0]
                                · linarith only [h390, h393, h400, h401, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h457 | h457
                                · linarith only [h390, h392, h400, h457, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h459 | h459
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h460 | h460
                                    · rcases h4bigk with h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h386, hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h390, h392, h459, hc45, hlam, hphi, ht0b, ht5b, p461_1, u0elo1]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h390, h392, h457, h460, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p461_1, u0elo1]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        rcases p461_3 (m.d 0 4) (by simp) with h466 | h466
                                        · rcases p461_3 (m.d 1 4) (by simp) with h467 | h467
                                          · rcases p461_3 (m.d 2 4) (by simp) with h468 | h468
                                            · linarith only [h391, h468, hlam]
                                            · linarith only [h459, h468, hlam]
                                          · linarith only [h399, h467, hlam]
                                        · linarith only [h466, hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h395, h397, hc12, hlam, hphi, ht01, p461_1, u0ehi8]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        rcases p461_3 (m.d 0 4) (by simp) with h475 | h475
                                        · linarith only [h386, h475, hlam]
                                        · linarith only [h391, h475, hlam]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        rcases p461_3 (m.d 0 4) (by simp) with h478 | h478
                                        · linarith only [h386, h478, hlam]
                                        · linarith only [h392, h478, hlam]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        rcases p461_3 (m.d 0 4) (by simp) with h481 | h481
                                        · linarith only [h386, h481, hlam]
                                        · linarith only [h394, h481, hlam]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h391, hlam, p461_1]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h396, hlam, p461_1]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h400, hlam, p461_1]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h391, hc45, hlam, hphi, ht0b, ht5b, p461_1, u0elo1]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h392, hlam, p461_1]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h397, hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h390, h392, hc24, hlam, hphi, ht0b, ht45, ht5b, p461_1, u0elo1]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h390, h392, hc45, hlam, hphi, ht0b, ht5b, p461_1, u0elo1]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h394, hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h399, hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h459, hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [h460, hlam, p461_0]
                                      · have p461_0 := h461c.1
                                        have p461_1 := h461c.2.1
                                        have p461_2 := h461c.2.2.1
                                        have p461_3 := h461c.2.2.2
                                        linarith only [hlam, p461_0]
                                    · linarith only [h391, h459, h460, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h500 | h500
                                    · linarith only [h390, h392, h400, h459, h500, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                    · linarith only [h390, h392, h394, h400, h500, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h390, h392, h394, h399, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi3]
                          · linarith only [h384, h398, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                        · linarith only [h384, h397, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h0, h396, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h395, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h508 | h508
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h509 | h509
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h510 | h510
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h511 | h511
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h512 | h512
                            · linarith only [h394, h508, h510, h512, hc12, hlam, hphi, ht01, u0ehi8]
                            · linarith only [h386, h512, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                          · linarith only [h390, h393, h511, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi2]
                        · linarith only [h384, h390, h392, h510, hlam, hphi, u0ehi5, u0elo1]
                      · linarith only [h391, h509, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                    · linarith only [h0, h390, h508, hlam, hphi, u0ehi5, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h519 | h519
                  · linarith only [h392, h393, h519, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h521 | h521
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h522 | h522
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h523 | h523
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h524 | h524
                          · linarith only [h393, h521, h524, hc12, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h384, h524, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                        · linarith only [h384, h392, h523, hlam, hphi, u0ehi5, u0elo2]
                      · linarith only [h391, h522, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                    · linarith only [h0, h390, h521, hlam, hphi, u0ehi5, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h530 | h530
                · rcases m.htr 0 4 5 (by decide) (by decide) with h531 | h531
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h532 | h532
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h533 | h533
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h534 | h534
                        · linarith only [h392, h532, h534, hc12, hlam, hphi, ht01, u0ehi7]
                        · linarith only [h384, h534, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h391, h533, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                    · linarith only [h0, h390, h532, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h392, h530, h531, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h540 | h540
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h541 | h541
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h542 | h542
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h543 | h543
                        · linarith only [h392, h541, h543, hc12, hlam, hphi, ht01, u0ehi7]
                        · linarith only [h384, h543, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h391, h542, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                    · linarith only [h0, h390, h541, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h548 | h548
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h549 | h549
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h550 | h550
                        · linarith only [h384, h392, h548, h550, hc12, hlam, hphi, ht01, u0ehi5]
                        · linarith only [h384, h550, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h384, h391, h392, h540, h549, hc45, hlam, hphi, ht12, ht23, ht34, u0ehi5, u0elo1, u1ehi1]
                    · linarith only [h0, h390, h548, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h555 | h555
              · linarith only [h390, h391, h555, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h557 | h557
                · rcases m.htr 0 4 5 (by decide) (by decide) with h558 | h558
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h559 | h559
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h560 | h560
                      · linarith only [h391, h560, hc12, hlam, hphi, ht01, u0ehi6]
                      · linarith only [h0, h560, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h390, h559, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h390, h391, h557, h558, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h565 | h565
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h566 | h566
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h567 | h567
                      · linarith only [h391, h567, hc12, hlam, hphi, ht01, u0ehi6]
                      · linarith only [h0, h567, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h390, h566, hlam, hphi, u0ehi5, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h571 | h571
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h572 | h572
                      · linarith only [h391, h572, hc12, hlam, hphi, ht01, u0ehi6]
                      · linarith only [h0, h572, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h390, h571, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h576 | h576
            · rcases m.htr 0 3 4 (by decide) (by decide) with h577 | h577
              · rcases m.htr 0 3 5 (by decide) (by decide) with h578 | h578
                · rcases m.htr 0 4 5 (by decide) (by decide) with h579 | h579
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h580 | h580
                    · linarith only [h390, h580, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h580, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h583 | h583
                    · linarith only [h390, h583, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h583, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h586 | h586
                  · linarith only [h390, h576, h578, h586, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                    · linarith only [h386, h390, h576, h588, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h588, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h390, h576, h577, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h592 | h592
              · rcases m.htr 0 3 5 (by decide) (by decide) with h593 | h593
                · rcases m.htr 0 4 5 (by decide) (by decide) with h594 | h594
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
                    · linarith only [h390, h595, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h595, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                    · linarith only [h0, h390, h598, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h598, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h601 | h601
                  · linarith only [h592, h593, h601, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h603 | h603
                    · linarith only [h0, h390, h603, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h603, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h606 | h606
                · rcases m.htr 0 4 5 (by decide) (by decide) with h607 | h607
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h608 | h608
                    · linarith only [h0, h390, h608, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h608, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h592, h606, h607, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h612 | h612
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h613 | h613
                    · linarith only [h0, h390, h613, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h613, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h616 | h616
                    · linarith only [h0, h390, h616, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h616, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
