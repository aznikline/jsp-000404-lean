import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3452000 in
set_option maxHeartbeats 3452000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h10, h15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h15, h7, hc23, hlam, hphi, u3elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                              · linarith only [h0, h10, h18, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h18, h7, hc23, hlam, hphi, u3elo0]
                          · linarith only [h13, h8, hc13, hlam, hphi, u3elo0]
                        · linarith only [h10, h12, h7, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h10, h24, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                                    · linarith only [h1, h26, h32, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h2, h28, h32, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h24, h28, h31, hlam]
                                · linarith only [h10, h27, h30, hlam]
                              · linarith only [h10, h29, h7, hc13, hlam, hphi, u3elo0]
                            · linarith only [h24, h28, h7, h9, hc12, hlam, hphi, ht23, u3elo0]
                          · linarith only [h0, h24, h26, h27, h5, h8, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, u1elo0, u3elo0]
                        · linarith only [h26, h7, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
                            · linarith only [h2, h45, h9, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                              · linarith only [h0, h41, h47, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h1, h43, h47, hc23, hlam, hphi, u3elo0]
                          · linarith only [h44, h8, hc13, hlam, hphi, u3elo0]
                        · linarith only [h41, h43, h7, hc23, hlam, hphi, u3elo0]
                      · linarith only [h41, h42, h5, h9, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
                      · linarith only [h0, h4, h41, h53, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                            · linarith only [h1, h55, h57, h9, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                                  · linarith only [h5, h61, h9, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                                    · linarith only [h5, h53, h63, h9, hc12, hlam, hphi, ht23, u3elo3]
                                    · rcases h0bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h4, h41, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p65_1, u1elo0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h1, h56, hc35, hlam, hphi, ht01, ht0b, ht5b, p65_1, u1elo0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h5, h53, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p65_1, u1elo0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h5, h53, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p65_1, u1elo0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h5, h53, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1, u0elo1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h5, h53, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p65_1, u1elo0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h5, h53, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p65_1, u1elo0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h1, hlam, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h4, hlam, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h5, h53, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1, u0elo2]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h5, h53, h9, hc12, hlam, hphi, ht23, p65_1, u3elo0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h2, hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h5, hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h7, hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h9, hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h3, hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h6, hlam, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h8, hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h5, h53, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1, u0elo4]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [hlam, p65_0]
                                · linarith only [h53, h59, h60, hc12, hlam, hphi, ht23, u3elo4]
                              · linarith only [h55, h59, hc23, hlam, hphi, u3elo1]
                          · linarith only [h56, h8, hc13, hlam, hphi, u3elo0]
                        · linarith only [h41, h55, h7, hc12, hlam, hphi, ht23, u3elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h95 | h95
                  · linarith only [h7, h8, h95, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                          · linarith only [h1, h100, h8, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                            · linarith only [h102, h2, h95, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                              · linarith only [h0, h104, h97, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h1, h104, h8, h99, hc23, hlam, hphi, u3elo4]
                        · linarith only [h7, h8, h99, hc13, hlam, hphi, u3elo4]
                      · linarith only [h5, h7, h8, h98, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h4, h8, h97, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h110 | h110
                · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                        · linarith only [h110, h114, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                              · linarith only [h0, h1, h112, h116, h118, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                                · linarith only [h0, h113, h118, h120, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h1, h116, h120, h7, hc23, hlam, hphi, u3elo3]
                            · linarith only [h111, h114, h116, h117, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h110, h112, h116, hc23, hlam, hphi, u3elo0]
                      · linarith only [h112, h113, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h112, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h110, h111, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h130 | h130
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                        · linarith only [h131, h7, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                          · linarith only [h1, h110, h133, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                              · linarith only [h1, h129, h136, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                                · linarith only [h1, h110, h129, h138, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
                                  · linarith only [h0, h130, h140, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h135, h140, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · linarith only [h128, h131, h135, h7, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h129, h130, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h129, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h147 | h147
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
                        · linarith only [h148, h7, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h150 | h150
                          · linarith only [h110, h128, h148, h150, h2, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                            · linarith only [h128, h152, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                              · linarith only [h1, h146, h154, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                                · linarith only [h1, h110, h146, h156, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h158 | h158
                                  · linarith only [h0, h1, h128, h146, h158, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h160 | h160
                                    · linarith only [h1, h128, h146, h160, h7, hc23, hlam, hphi, u3elo3]
                                    · rcases h0bigk with h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p162_1, u1elo0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h165 | h165
                                        · rcases p162_3 (m.d 0 2) (by simp) with h166 | h166
                                          · linarith only [h0, h166, hlam]
                                          · linarith only [h166, h4, hlam]
                                        · linarith only [h1, h165, hlam]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h170 | h170
                                        · rcases p162_3 (m.d 0 2) (by simp) with h171 | h171
                                          · linarith only [h0, h171, hlam]
                                          · linarith only [h171, h5, hlam]
                                        · linarith only [h170, h2, hlam]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h175 | h175
                                        · rcases p162_3 (m.d 0 2) (by simp) with h176 | h176
                                          · linarith only [h0, h176, hlam]
                                          · linarith only [h176, h6, hlam]
                                        · linarith only [h175, h3, hlam]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h0, hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h182 | h182
                                        · rcases p162_3 (m.d 0 2) (by simp) with h183 | h183
                                          · rcases p162_3 (m.d 0 3) (by simp) with h184 | h184
                                            · linarith only [h184, h4, hlam]
                                            · rcases p162_3 (m.d 0 4) (by simp) with h186 | h186
                                              · linarith only [h186, h5, hlam]
                                              · linarith only [h186, h7, hlam]
                                          · linarith only [h183, h4, hlam]
                                        · linarith only [h1, h182, hlam]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h191 | h191
                                        · rcases p162_3 (m.d 0 2) (by simp) with h192 | h192
                                          · rcases p162_3 (m.d 0 3) (by simp) with h193 | h193
                                            · linarith only [h193, h4, hlam]
                                            · rcases p162_3 (m.d 0 4) (by simp) with h195 | h195
                                              · linarith only [h195, h5, hlam]
                                              · rcases p162_3 (m.d 0 5) (by simp) with h197 | h197
                                                · linarith only [h197, h6, hlam]
                                                · linarith only [h128, h197, hlam]
                                          · linarith only [h192, h5, hlam]
                                        · linarith only [h191, h2, hlam]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h202 | h202
                                        · rcases p162_3 (m.d 0 2) (by simp) with h203 | h203
                                          · rcases p162_3 (m.d 0 3) (by simp) with h204 | h204
                                            · linarith only [h204, h4, hlam]
                                            · rcases p162_3 (m.d 0 4) (by simp) with h206 | h206
                                              · linarith only [h206, h5, hlam]
                                              · rcases p162_3 (m.d 0 5) (by simp) with h208 | h208
                                                · linarith only [h208, h6, hlam]
                                                · rcases h4bigk with h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [hlam, p210_0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h128, hc14, hlam, hphi, ht0b, ht45, ht5b, p162_1, p210_1, u0elo1]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h0, h128, h154, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p162_1, p210_1, u1elo0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h7, hlam, p210_0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h128, hlam, p210_0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h2, hlam, p210_1]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [hlam, p210_0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h154, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p210_1, u1elo0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h148, hlam, p210_1]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h152, hlam, p210_0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h5, hlam, p210_1]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h147, hlam, p210_1]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [hlam, p210_0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h154, hlam, p210_1]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h158, hlam, p210_0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h7, hc03, hlam, hphi, p210_1, u3elo3]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h160, hc14, hc45, hlam, hphi, p210_1]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h154, h160, hc23, hlam, hphi, p210_1, u3elo4]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [hlam, p210_0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h160, hlam, p210_0]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    rcases p210_3 (m.d 0 4) (by simp) with h231 | h231
                                                    · linarith only [h231, hlam, p210_0]
                                                    · rcases p210_3 (m.d 1 4) (by simp) with h233 | h233
                                                      · linarith only [h152, h233, hlam]
                                                      · rcases p210_3 (m.d 2 4) (by simp) with h235 | h235
                                                        · linarith only [h158, h235, hlam]
                                                        · rcases p210_3 (m.d 3 4) (by simp) with h237 | h237
                                                          · linarith only [h160, h237, hlam]
                                                          · linarith only [h237, h7, hlam]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    rcases p210_3 (m.d 0 4) (by simp) with h240 | h240
                                                    · linarith only [h128, h240, hlam]
                                                    · linarith only [h2, h240, hlam]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    rcases p210_3 (m.d 0 4) (by simp) with h243 | h243
                                                    · linarith only [h128, h243, hlam]
                                                    · linarith only [h243, h5, hlam]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [h1, h146, h7, hc23, hc45, hlam, hphi, ht34, p210_1]
                                                  · have p210_0 := h210c.1
                                                    have p210_1 := h210c.2.1
                                                    have p210_2 := h210c.2.2.1
                                                    have p210_3 := h210c.2.2.2
                                                    linarith only [hlam, p210_0]
                                          · linarith only [h203, h6, hlam]
                                        · linarith only [h202, h3, hlam]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h1, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h4, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h7, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h110, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h2, hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h5, hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h1, h146, h7, hc23, hlam, hphi, p162_1, u3elo3]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h128, hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h3, hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h6, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h1, h110, h146, hc23, hlam, hphi, p162_1, u3elo4]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h110, h147, h154, h2, hc23, hlam, hphi, p162_1, u3elo4]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [hlam, p162_0]
                      · linarith only [h0, h146, h147, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h146, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h267 | h267
              · rcases m.htr 0 3 5 (by decide) (by decide) with h268 | h268
                · linarith only [h268, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h270 | h270
                  · linarith only [h267, h270, h4, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h272 | h272
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h275 | h275
                          · linarith only [h1, h268, h275, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                            · linarith only [h2, h270, h277, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                              · linarith only [h0, h272, h279, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h267, h268, h279, hc23, hlam, hphi, u3elo4]
                        · linarith only [h267, h268, h274, hc13, hlam, hphi, u3elo4]
                      · linarith only [h273, h5, h6, hc12, hc25, hlam, hphi]
                    · linarith only [h268, h272, h4, h6, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h285 | h285
                · linarith only [h267, h285, h4, h6, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h287 | h287
                  · linarith only [h287, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h289 | h289
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h290 | h290
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h291 | h291
                        · linarith only [h1, h267, h291, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h293 | h293
                          · linarith only [h0, h1, h267, h285, h289, h293, h6, hc23, hlam, hphi, u3elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                            · linarith only [h2, h287, h295, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h297 | h297
                              · linarith only [h0, h267, h289, h297, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h299 | h299
                                · linarith only [h1, h267, h285, h289, h299, h6, hc02, hlam, hphi, ht23, u3elo3]
                                · linarith only [h0, h290, h297, h299, h6, hc23, hlam, hphi, u3elo4]
                      · linarith only [h290, h5, h6, hc12, hc25, hlam, hphi]
                    · linarith only [h285, h289, h4, h6, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h304 | h304
            · rcases m.htr 0 3 4 (by decide) (by decide) with h305 | h305
              · linarith only [h305, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h307 | h307
                · rcases m.htr 0 4 5 (by decide) (by decide) with h308 | h308
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h309 | h309
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h310 | h310
                      · linarith only [h0, h310, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h312 | h312
                        · linarith only [h1, h305, h312, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h314 | h314
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h316 | h316
                              · linarith only [h0, h305, h309, h316, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h0, h309, h316, h5, hc23, hlam, hphi, u3elo3]
                            · linarith only [h305, h307, h308, h309, h310, h315, hc23, hlam, hphi, u3elo3]
                          · linarith only [h305, h307, h314, hc13, hlam, hphi, u3elo3]
                    · linarith only [h309, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h305, h307, h308, h4, h5, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h323 | h323
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h324 | h324
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h325 | h325
                      · linarith only [h0, h325, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h327 | h327
                        · linarith only [h1, h305, h327, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h329 | h329
                          · linarith only [h1, h307, h329, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h332 | h332
                              · linarith only [h0, h305, h324, h332, h5, hlam]
                              · linarith only [h0, h324, h332, h5, hc23, hlam, hphi, u3elo3]
                            · linarith only [h323, h324, h325, h331, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h324, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h304, h323, h5, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h338 | h338
              · linarith only [h338, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h340 | h340
                · linarith only [h304, h338, h340, h4, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h342 | h342
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h343 | h343
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h344 | h344
                      · linarith only [h0, h344, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h346 | h346
                        · linarith only [h1, h338, h346, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                          · linarith only [h1, h340, h348, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h350 | h350
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h351 | h351
                              · linarith only [h0, h338, h343, h351, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h0, h343, h351, h5, hc23, hlam, hphi, u3elo3]
                            · linarith only [h338, h342, h343, h344, h350, hc23, hlam, hphi, u3elo3]
                    · linarith only [h343, h4, h5, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h356 | h356
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h357 | h357
                      · linarith only [h0, h357, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h359 | h359
                        · linarith only [h1, h338, h359, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                          · linarith only [h0, h1, h338, h340, h342, h356, h361, h5, hc23, hlam, hphi, u3elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                            · linarith only [h2, h342, h363, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h365 | h365
                              · linarith only [h0, h338, h356, h365, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h365, h4, h5, hc23, hlam, hphi, u3elo3]
                    · linarith only [h356, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h369 | h369
          · rcases m.htr 0 2 5 (by decide) (by decide) with h370 | h370
            · rcases m.htr 0 3 4 (by decide) (by decide) with h371 | h371
              · rcases m.htr 0 3 5 (by decide) (by decide) with h372 | h372
                · rcases m.htr 0 4 5 (by decide) (by decide) with h373 | h373
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h374 | h374
                    · linarith only [h369, h374, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h376 | h376
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h377 | h377
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h378 | h378
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h379 | h379
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h382 | h382
                                  · linarith only [h0, h376, h382, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                  · linarith only [h369, h373, h380, h382, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h381, h4, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h2, h369, h379, h380, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · linarith only [h369, h373, h379, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h372, h378, hc13, hlam, hphi, u3elo0]
                        · linarith only [h371, h374, h376, h377, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h369, h376, h4, hc12, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h391 | h391
                    · linarith only [h369, h391, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h393 | h393
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h394 | h394
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h395 | h395
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h396 | h396
                            · linarith only [h2, h373, h396, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h398 | h398
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h399 | h399
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h400 | h400
                                  · linarith only [h0, h373, h393, h400, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h402 | h402
                                    · linarith only [h3, h369, h373, h398, h4, h402, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                    · rcases h0bigk with h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h0, h393, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p404_1, u1elo0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h0, h393, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p404_1, u1elo0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        rcases p404_3 (m.d 0 1) (by simp) with h408 | h408
                                        · rcases p404_3 (m.d 0 2) (by simp) with h409 | h409
                                          · linarith only [h0, h409, hlam]
                                          · linarith only [h369, h409, hlam]
                                        · linarith only [h2, h408, hlam]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        rcases p404_3 (m.d 0 1) (by simp) with h413 | h413
                                        · rcases p404_3 (m.d 0 2) (by simp) with h414 | h414
                                          · linarith only [h0, h414, hlam]
                                          · linarith only [h370, h414, hlam]
                                        · linarith only [h3, h413, hlam]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h0, hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h4, hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h2, h393, h398, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p404_1, u3elo2]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h2, h373, h393, h398, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p404_1, u3elo2]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h1, hlam, p404_1]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [hc02, hlam, hphi, ht23, p404_1, u3elo0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        rcases p404_3 (m.d 0 1) (by simp) with h426 | h426
                                        · rcases p404_3 (m.d 0 2) (by simp) with h427 | h427
                                          · linarith only [h4, h427, hlam]
                                          · linarith only [h369, h427, hlam]
                                        · linarith only [h2, h426, hlam]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        rcases p404_3 (m.d 0 1) (by simp) with h431 | h431
                                        · rcases p404_3 (m.d 0 2) (by simp) with h432 | h432
                                          · linarith only [h4, h432, hlam]
                                          · linarith only [h370, h432, hlam]
                                        · linarith only [h3, h431, hlam]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h2, hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h369, hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h371, hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h373, hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h3, hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h370, hlam, p404_1]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h372, hlam, p404_0]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [h2, h370, h393, h398, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p404_1, u3elo2]
                                      · have p404_0 := h404c.1
                                        have p404_1 := h404c.2.1
                                        have p404_2 := h404c.2.2.1
                                        have p404_3 := h404c.2.2.2
                                        linarith only [hlam, p404_0]
                                · linarith only [h399, h4, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h398, h4, hc02, hlam, hphi, ht23, u3elo3]
                          · linarith only [h372, h395, hc13, hlam, hphi, u3elo0]
                        · linarith only [h371, h391, h393, h394, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h369, h393, h4, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h370, h372, h4, hlam]
              · linarith only [h369, h371, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h453 | h453
              · rcases m.htr 0 3 5 (by decide) (by decide) with h454 | h454
                · rcases m.htr 0 4 5 (by decide) (by decide) with h455 | h455
                  · linarith only [h369, h370, h455, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
                    · linarith only [h0, h4, h457, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h459 | h459
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h461 | h461
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h462 | h462
                            · linarith only [h2, h455, h462, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h465 | h465
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h466 | h466
                                  · linarith only [h455, h459, h466, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h468 | h468
                                    · linarith only [h370, h466, h468, hc02, hlam, hphi, ht23, u3elo3]
                                    · rcases h0bigk with h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, h459, h464, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p470_1, u1elo0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, h370, h454, h459, h464, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p470_1, u1elo0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        rcases p470_3 (m.d 0 1) (by simp) with h474 | h474
                                        · rcases p470_3 (m.d 0 2) (by simp) with h475 | h475
                                          · linarith only [h0, h475, hlam]
                                          · linarith only [h369, h475, hlam]
                                        · linarith only [h2, h474, hlam]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, h370, h459, h464, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p470_1, u1elo0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h4, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h2, h370, h466, hc14, hc45, hlam, hphi, p470_1]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h370, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h1, hlam, p470_1]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, h459, hc24, hlam, hphi, ht0b, ht45, ht5b, p470_1, u0elo2]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        rcases p470_3 (m.d 0 1) (by simp) with h488 | h488
                                        · rcases p470_3 (m.d 0 2) (by simp) with h489 | h489
                                          · linarith only [h4, h489, hlam]
                                          · linarith only [h369, h489, hlam]
                                        · linarith only [h2, h488, hlam]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h370, h4, hc02, hlam, hphi, ht23, p470_1, u3elo2]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h2, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h369, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h453, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h455, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h3, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h3, h369, h464, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p470_1, u1elo0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h454, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        rcases p470_3 (m.d 0 1) (by simp) with h502 | h502
                                        · rcases p470_3 (m.d 0 2) (by simp) with h503 | h503
                                          · linarith only [h370, h503, hlam]
                                          · linarith only [h369, h503, hlam]
                                        · linarith only [h2, h502, hlam]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [hlam, p470_0]
                                · linarith only [h0, h4, h459, h464, h465, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · linarith only [h0, h4, h459, h464, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h4, h454, h461, hc13, hlam, hphi, u3elo2]
                        · linarith only [h4, h453, h457, h459, h460, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h369, h4, h459, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h513 | h513
                  · linarith only [h369, h370, h513, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h515 | h515
                    · linarith only [h0, h4, h515, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h517 | h517
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h518 | h518
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h519 | h519
                          · linarith only [h0, h4, h454, h519, hc12, hlam, hphi, ht23, u3elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                            · linarith only [h2, h513, h521, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h524 | h524
                                · linarith only [h0, h4, h454, h517, h523, h524, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h0, h4, h517, h523, h524, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · linarith only [h4, h523, hc02, hlam, hphi, ht23, u3elo3]
                        · linarith only [h453, h515, h517, h518, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h369, h4, h517, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h369, h4, h453, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h531 | h531
            · rcases m.htr 0 3 4 (by decide) (by decide) with h532 | h532
              · rcases m.htr 0 3 5 (by decide) (by decide) with h533 | h533
                · rcases m.htr 0 4 5 (by decide) (by decide) with h534 | h534
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                    · linarith only [h0, h4, h535, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h537 | h537
                      · linarith only [h369, h535, h537, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h539 | h539
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h540 | h540
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h541 | h541
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h542 | h542
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h543 | h543
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h544 | h544
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h545 | h545
                                    · linarith only [h1, h539, h545, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h1, h539, h541, h545, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h369, h531, h541, h544, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                                · linarith only [h4, h531, h543, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                              · linarith only [h4, h531, h542, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · linarith only [h4, h531, h534, h537, h541, hc12, hlam, hphi, ht23, u3elo2]
                          · linarith only [h4, h533, h540, hc13, hlam, hphi, u3elo2]
                        · linarith only [h4, h532, h535, h539, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h369, h531, h534, hlam]
                · linarith only [h369, h531, h532, h533, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h556 | h556
                · rcases m.htr 0 4 5 (by decide) (by decide) with h557 | h557
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h558 | h558
                    · linarith only [h0, h4, h558, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h560 | h560
                      · linarith only [h0, h369, h560, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h562 | h562
                        · linarith only [h1, h532, h562, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h564 | h564
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h565 | h565
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h566 | h566
                              · linarith only [h4, h532, h566, hc02, hlam, hphi, ht23, u3elo2]
                              · linarith only [h4, h566, hc02, hlam, hphi, ht23, u3elo3]
                            · linarith only [h557, h562, h564, h565, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h532, h556, h564, hc13, hlam, hphi, u3elo3]
                  · linarith only [h369, h531, h557, hlam]
                · linarith only [h4, h531, h556, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h573 | h573
              · rcases m.htr 0 3 5 (by decide) (by decide) with h574 | h574
                · rcases m.htr 0 4 5 (by decide) (by decide) with h575 | h575
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h576 | h576
                    · linarith only [h0, h4, h576, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h578 | h578
                      · linarith only [h0, h369, h578, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h580 | h580
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h581 | h581
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h582 | h582
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h583 | h583
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h584 | h584
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h585 | h585
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h586 | h586
                                    · linarith only [h1, h580, h586, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h2, h582, h586, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h3, h369, h582, h585, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h0, h1, h369, h581, h583, h584, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h0, h4, h583, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h4, h573, h575, h578, h582, hc12, hlam, hphi, ht23, u3elo2]
                          · linarith only [h4, h574, h580, h581, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h4, h573, h580, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
                    · linarith only [h0, h4, h573, h595, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h597 | h597
                      · linarith only [h369, h595, h597, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h599 | h599
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h600 | h600
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h601 | h601
                            · linarith only [h2, h575, h601, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h603 | h603
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h604 | h604
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h605 | h605
                                  · linarith only [h0, h369, h575, h603, h605, hc12, hlam, hphi, ht23, u3elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                                    · linarith only [h1, h599, h605, h607, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · rcases h0bigk with h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        rcases p609_3 (m.d 0 1) (by simp) with h611 | h611
                                        · rcases p609_3 (m.d 0 2) (by simp) with h612 | h612
                                          · linarith only [h0, h612, hlam]
                                          · rcases p609_3 (m.d 0 3) (by simp) with h614 | h614
                                            · linarith only [h1, h614, hlam]
                                            · linarith only [h4, h614, hlam]
                                        · linarith only [h0, h611, hlam]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h1, h600, h607, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p609_1, u1elo0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        rcases p609_3 (m.d 0 1) (by simp) with h619 | h619
                                        · rcases p609_3 (m.d 0 2) (by simp) with h620 | h620
                                          · linarith only [h0, h620, hlam]
                                          · rcases p609_3 (m.d 0 3) (by simp) with h622 | h622
                                            · linarith only [h1, h622, hlam]
                                            · linarith only [h573, h622, hlam]
                                        · linarith only [h2, h619, hlam]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        rcases p609_3 (m.d 0 1) (by simp) with h626 | h626
                                        · rcases p609_3 (m.d 0 2) (by simp) with h627 | h627
                                          · linarith only [h0, h627, hlam]
                                          · rcases p609_3 (m.d 0 3) (by simp) with h629 | h629
                                            · linarith only [h1, h629, hlam]
                                            · linarith only [h574, h629, hlam]
                                        · linarith only [h3, h626, hlam]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h4, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h369, hlam, p609_1]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h531, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h1, hlam, p609_1]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, p609_1, u3elo0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, h369, h4, hc12, hlam, hphi, ht23, p609_1, u3elo2]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, h369, h4, h575, hc12, hlam, hphi, ht23, p609_1, u3elo2]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h2, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, h369, h605, hc12, hc45, hlam, hphi, ht23, ht34, p609_1]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h573, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h575, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h3, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, h4, h574, hc12, hlam, hphi, ht23, p609_1, u3elo2]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h574, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h2, h4, h574, h597, hc12, hlam, hphi, ht23, p609_1, u3elo2]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [hlam, p609_0]
                                · linarith only [h4, h600, h604, hc03, hlam, hphi, u3elo1]
                              · linarith only [h0, h4, h603, hc12, hlam, hphi, ht23, u3elo3]
                          · linarith only [h574, h599, h600, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h4, h573, h595, h599, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h657 | h657
                  · linarith only [h573, h574, h657, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                    · linarith only [h0, h4, h659, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h661 | h661
                      · linarith only [h369, h659, h661, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h663 | h663
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h664 | h664
                          · linarith only [h1, h574, h664, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h666 | h666
                            · linarith only [h2, h657, h666, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h669 | h669
                                · linarith only [h574, h669, hc03, hlam, hphi, u3elo2]
                                · linarith only [h0, h4, h669, hc12, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h1, h4, h663, h668, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h573, h574, h663, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h674 | h674
                · rcases m.htr 0 4 5 (by decide) (by decide) with h675 | h675
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h676 | h676
                    · linarith only [h0, h4, h676, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h678 | h678
                      · linarith only [h0, h369, h678, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h680 | h680
                        · linarith only [h531, h573, h674, h680, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h682 | h682
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h683 | h683
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h684 | h684
                              · linarith only [h1, h573, h682, h684, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h0, h4, h684, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h675, h680, h682, h683, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h674, h682, hc13, hlam, hphi, u3elo0]
                  · linarith only [h573, h674, h675, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h690 | h690
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h691 | h691
                    · linarith only [h0, h4, h691, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h693 | h693
                      · linarith only [h369, h691, h693, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h695 | h695
                        · linarith only [h1, h573, h695, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h697 | h697
                          · linarith only [h1, h674, h697, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h699 | h699
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h700 | h700
                              · linarith only [h573, h700, hc03, hlam, hphi, u3elo2]
                              · linarith only [h0, h4, h700, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h573, h690, h693, h699, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h704 | h704
                    · linarith only [h0, h4, h704, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h706 | h706
                      · linarith only [h0, h369, h706, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h708 | h708
                        · linarith only [h1, h4, h573, h708, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h710 | h710
                          · linarith only [h1, h674, h710, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h712 | h712
                            · linarith only [h2, h690, h712, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h714 | h714
                              · linarith only [h0, h4, h573, h714, hc12, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h4, h714, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h717 | h717
        · rcases m.htr 0 2 4 (by decide) (by decide) with h718 | h718
          · rcases m.htr 0 2 5 (by decide) (by decide) with h719 | h719
            · linarith only [h0, h3, h719, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h721 | h721
              · rcases m.htr 0 3 5 (by decide) (by decide) with h722 | h722
                · linarith only [h1, h3, h722, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h724 | h724
                  · linarith only [h0, h3, h717, h721, h724, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h726 | h726
                    · linarith only [h0, h3, h726, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h717, h719, h726, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h729 | h729
                · linarith only [h1, h3, h721, h729, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h731 | h731
                  · linarith only [h0, h3, h718, h731, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h733 | h733
                    · linarith only [h0, h3, h733, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h717, h719, h733, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h736 | h736
            · linarith only [h2, h3, h718, h736, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h738 | h738
              · linarith only [h717, h718, h738, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h740 | h740
                · linarith only [h2, h3, h717, h718, h738, h740, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h742 | h742
                  · linarith only [h2, h3, h742, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h744 | h744
                    · linarith only [h0, h3, h744, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h2, h3, h717, h718, h744, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h747 | h747
          · rcases m.htr 0 2 5 (by decide) (by decide) with h748 | h748
            · linarith only [h0, h3, h748, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h750 | h750
              · rcases m.htr 0 3 5 (by decide) (by decide) with h751 | h751
                · linarith only [h1, h3, h751, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h753 | h753
                  · linarith only [h0, h3, h717, h747, h751, h753, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h755 | h755
                    · linarith only [h0, h717, h751, h755, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h757 | h757
                      · linarith only [h0, h3, h757, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · linarith only [h717, h747, h751, h757, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h717, h747, h750, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h761 | h761
            · linarith only [h1, h3, h717, h761, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h763 | h763
              · rcases m.htr 0 3 5 (by decide) (by decide) with h764 | h764
                · linarith only [h1, h3, h764, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h766 | h766
                  · linarith only [h0, h3, h763, h764, h766, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h768 | h768
                    · linarith only [h0, h747, h763, h764, h768, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h770 | h770
                      · linarith only [h0, h747, h770, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h772 | h772
                        · linarith only [h1, h3, h772, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · linarith only [h763, h764, h768, h772, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h775 | h775
                · linarith only [h0, h3, h763, h775, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h777 | h777
                  · linarith only [h2, h3, h777, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h779 | h779
                    · linarith only [h0, h717, h779, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h781 | h781
                      · linarith only [h0, h747, h781, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
                        · linarith only [h1, h3, h763, h783, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h785 | h785
                          · linarith only [h2, h3, h775, h783, h785, hlam]
                          · linarith only [h2, h3, h779, h783, h785, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h788 | h788
      · rcases m.htr 0 2 3 (by decide) (by decide) with h789 | h789
        · rcases m.htr 0 2 4 (by decide) (by decide) with h790 | h790
          · linarith only [h0, h2, h790, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h792 | h792
            · rcases m.htr 0 3 4 (by decide) (by decide) with h793 | h793
              · linarith only [h1, h2, h793, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h795 | h795
                · rcases m.htr 0 4 5 (by decide) (by decide) with h796 | h796
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h797 | h797
                    · linarith only [h0, h2, h797, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h2, h789, h797, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h1, h2, h793, h795, h796, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h801 | h801
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                    · linarith only [h0, h2, h802, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h789, h790, h802, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2, h792, h801, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h806 | h806
              · linarith only [h1, h2, h806, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h808 | h808
                · linarith only [h789, h792, h808, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h810 | h810
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h811 | h811
                    · linarith only [h0, h2, h811, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h2, h788, h789, h792, h811, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h2, h788, h810, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h815 | h815
          · linarith only [h0, h2, h815, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h817 | h817
            · rcases m.htr 0 3 4 (by decide) (by decide) with h818 | h818
              · linarith only [h1, h2, h818, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h820 | h820
                · rcases m.htr 0 4 5 (by decide) (by decide) with h821 | h821
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h822 | h822
                    · linarith only [h0, h2, h822, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h824 | h824
                      · linarith only [h1, h2, h815, h822, h824, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h826 | h826
                        · linarith only [h1, h2, h818, h826, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                        · linarith only [h1, h2, h822, h826, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1, h2, h789, h817, h821, hc13, hlam, hphi, u3elo2]
                · linarith only [h789, h817, h820, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h831 | h831
              · linarith only [h1, h2, h831, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h833 | h833
                · rcases m.htr 0 4 5 (by decide) (by decide) with h834 | h834
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h835 | h835
                    · linarith only [h0, h817, h831, h833, h835, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h837 | h837
                      · linarith only [h0, h2, h837, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h839 | h839
                        · linarith only [h1, h2, h817, h831, h833, h839, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                        · linarith only [h1, h2, h839, hc13, hlam, hphi, u3elo3]
                  · linarith only [h2, h788, h834, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h843 | h843
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h844 | h844
                    · linarith only [h0, h789, h844, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h846 | h846
                      · linarith only [h1, h2, h844, h846, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h848 | h848
                        · linarith only [h1, h2, h848, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · linarith only [h1, h2, h844, h848, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h2, h788, h843, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h852 | h852
        · rcases m.htr 0 2 4 (by decide) (by decide) with h853 | h853
          · linarith only [h0, h2, h853, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h855 | h855
            · linarith only [h0, h788, h855, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h857 | h857
              · linarith only [h1, h2, h857, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h859 | h859
                · linarith only [h0, h788, h852, h859, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h861 | h861
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h862 | h862
                    · linarith only [h0, h2, h862, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h2, h852, h862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h865 | h865
                    · linarith only [h0, h2, h865, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h2, h852, h865, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h868 | h868
          · linarith only [h0, h2, h868, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h870 | h870
            · linarith only [h1, h788, h852, h870, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h872 | h872
              · linarith only [h1, h2, h872, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h874 | h874
                · linarith only [h0, h788, h872, h874, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h876 | h876
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h877 | h877
                    · linarith only [h0, h788, h877, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h879 | h879
                      · linarith only [h868, h877, h879, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h881 | h881
                        · linarith only [h1, h788, h872, h881, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                        · linarith only [h1, h2, h877, h881, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h884 | h884
                    · linarith only [h0, h852, h884, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h886 | h886
                      · linarith only [h0, h788, h886, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h888 | h888
                        · linarith only [h1, h788, h888, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · linarith only [h1, h2, h888, hc13, hlam, hphi, u3elo3]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
