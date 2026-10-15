import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3024000 in
theorem r1l7_10_12_23_L_0_L_I_M_LI_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
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
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
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
                        · linarith only [h12, h5, hc23, hlam, hphi, u3elo0]
                      · linarith only [h11, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h10, h5, h7, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h4, h8, h9, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h3, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h19, h2, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
                  · linarith only [h0, h19, h21, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                              · linarith only [h1, h23, h28, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h0, h2, h25, h27, h28, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                              · linarith only [h19, h27, h31, hc12, hlam, hphi, ht23, u3elo3]
                              · rcases h2bigk with h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  rcases p33_3 (m.d 0 2) (by simp) with h35 | h35
                                  · rcases p33_3 (m.d 1 2) (by simp) with h36 | h36
                                    · linarith only [h0, h36, hlam]
                                    · rcases p33_3 (m.d 2 3) (by simp) with h38 | h38
                                      · linarith only [h2, h38, hlam]
                                      · linarith only [h38, h7, hlam]
                                  · linarith only [h0, h35, hlam]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h0, h24, h31, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p33_1, u0elo0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h0, h19, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p33_1, u0elo0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h0, h19, h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p33_1, u0elo0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h0, hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h7, hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h19, hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h21, hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h2, hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p33_1, u3elo2]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h0, h19, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p33_1, u0elo0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h0, h19, h2, h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p33_1, u0elo0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h3, hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h27, hc12, hc45, hlam, hphi, ht23, ht34, p33_1]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h25, hlam, p33_1]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h27, hlam, p33_1]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h4, hlam, p33_0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h0, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p33_1, u0elo0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h26, hlam, p33_1]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [h0, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, p33_1, u0elo0]
                                · have p33_0 := h33c.1
                                  have p33_1 := h33c.2.1
                                  have p33_2 := h33c.2.2.1
                                  have p33_3 := h33c.2.2.2
                                  linarith only [hlam, p33_0]
                          · linarith only [h24, h26, hc23, hlam, hphi, u3elo1]
                        · linarith only [h25, h5, h7, hc13, hlam, hphi, u3elo0]
                      · linarith only [h23, h24, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · linarith only [h23, h5, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
              · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
                · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
                      · linarith only [h6, h73, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                        · linarith only [h0, h69, h75, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h72, h75, hc23, hlam, hphi, u3elo0]
                    · linarith only [h5, h6, h72, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h4, h70, h71, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h3, h69, h70, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h2, h6, h69, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h82 | h82
            · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
              · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
                · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                    · linarith only [h5, h86, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                        · linarith only [h0, h1, h5, h83, h88, h89, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
                          · linarith only [h0, h84, h89, h91, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h1, h5, h88, h91, hc23, hlam, hphi, u3elo3]
                      · linarith only [h5, h82, h88, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h4, h84, h85, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h3, h83, h84, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h2, h5, h83, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
              · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
                · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                    · linarith only [h101, h5, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                      · linarith only [h1, h103, h82, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                        · linarith only [h1, h105, h5, h98, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                          · linarith only [h1, h107, h82, h98, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h109 | h109
                            · linarith only [h0, h109, h99, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h111 | h111
                              · linarith only [h105, h109, h111, hc23, hlam, hphi, u3elo3]
                              · rcases h2bigk with h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h100, hc25, hlam, hphi, ht0b, ht5b, p113_1, u0elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 2) (by simp) with h116 | h116
                                  · rcases p113_3 (m.d 1 2) (by simp) with h117 | h117
                                    · linarith only [h0, h117, hlam]
                                    · linarith only [h117, h98, hlam]
                                  · linarith only [h116, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 2) (by simp) with h121 | h121
                                  · rcases p113_3 (m.d 1 2) (by simp) with h122 | h122
                                    · linarith only [h0, h122, hlam]
                                    · linarith only [h122, h99, hlam]
                                  · linarith only [h121, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 2) (by simp) with h126 | h126
                                  · rcases p113_3 (m.d 1 2) (by simp) with h127 | h127
                                    · linarith only [h0, h127, hlam]
                                    · linarith only [h100, h127, hlam]
                                  · linarith only [h126, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1, u0elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h105, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1, u0elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h105, h109, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1, u0elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h2, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h98, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h105, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h107, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h3, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h99, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1, u0elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h109, hlam, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h4, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h100, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h100, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1, u0elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h100, hc24, hlam, hphi, ht0b, ht45, ht5b, p113_1, u0elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                  · linarith only [h100, h4, h82, h98, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h3, h98, h99, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h2, h5, h98, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h154 | h154
          · rcases m.htr 0 3 5 (by decide) (by decide) with h155 | h155
            · linarith only [h155, h2, h4, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h157 | h157
              · rcases m.htr 1 2 4 (by decide) (by decide) with h158 | h158
                · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                  · linarith only [h0, h159, h4, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                      · linarith only [h1, h155, h162, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                        · linarith only [h0, h157, h164, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h155, h161, h164, hc23, hlam, hphi, u3elo4]
                    · linarith only [h154, h155, h161, hc13, hlam, hphi, u3elo4]
                · linarith only [h158, h3, h4, hc12, hc25, hlam, hphi]
              · linarith only [h155, h157, h2, h4, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
            · linarith only [h154, h170, h2, h4, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h172 | h172
              · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
                · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                  · linarith only [h0, h174, h4, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h176 | h176
                    · linarith only [h154, h176, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h178 | h178
                      · linarith only [h0, h1, h154, h170, h172, h178, h4, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
                        · linarith only [h0, h154, h172, h180, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
                          · linarith only [h0, h170, h173, h180, h182, h4, hlam]
                          · linarith only [h0, h173, h180, h182, h4, hc23, hlam, hphi, u3elo4]
                · linarith only [h173, h3, h4, hc12, hc25, hlam, hphi]
              · linarith only [h170, h172, h2, h4, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h187 | h187
        · rcases m.htr 0 3 4 (by decide) (by decide) with h188 | h188
          · linarith only [h188, h2, h3, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h190 | h190
            · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
              · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
                · linarith only [h0, h192, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
                    · linarith only [h1, h188, h195, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                        · linarith only [h0, h188, h191, h198, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h191, h198, h3, hc23, hlam, hphi, u3elo3]
                      · linarith only [h188, h190, h197, hc13, hlam, hphi, u3elo3]
                  · linarith only [h187, h188, h191, h194, h3, hc23, hlam, hphi, u3elo3]
              · linarith only [h188, h191, h2, h3, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
              · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
                · linarith only [h0, h205, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h207 | h207
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
                    · linarith only [h188, h208, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                      · linarith only [h1, h190, h210, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                        · linarith only [h0, h1, h188, h190, h204, h212, h3, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h204, h212, h3, hc23, hlam, hphi, u3elo3]
                  · linarith only [h187, h204, h207, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h188, h2, h204, h3, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h217 | h217
          · linarith only [h2, h217, h3, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h219 | h219
            · linarith only [h187, h2, h217, h219, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
              · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                · linarith only [h0, h222, h3, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                  · linarith only [h0, h187, h224, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h226 | h226
                    · linarith only [h217, h226, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h228 | h228
                      · linarith only [h0, h1, h187, h219, h221, h228, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                        · linarith only [h0, h217, h221, h230, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h2, h230, h3, hc23, hlam, hphi, u3elo3]
              · linarith only [h2, h221, h3, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h234 | h234
      · rcases m.htr 0 2 5 (by decide) (by decide) with h235 | h235
        · rcases m.htr 0 3 4 (by decide) (by decide) with h236 | h236
          · rcases m.htr 0 3 5 (by decide) (by decide) with h237 | h237
            · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
              · linarith only [h0, h2, h238, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h242 | h242
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h243 | h243
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                            · linarith only [h0, h2, h240, h246, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                              · linarith only [h244, h246, h248, hlam]
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
                                  linarith only [h2, hc12, hlam, hphi, ht23, p250_1, u3elo2]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h2, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h2, h244, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p250_1, u3elo2]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h2, h244, h246, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p250_1, u3elo2]
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
                                  linarith only [h238, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h0, h244, hc34, hlam, hphi, ht0b, ht45, ht5b, p250_1, u0elo0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h0, h2, h244, h246, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p250_1, u3elo2]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p250_1, u3elo2]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p250_1, u3elo2]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  rcases p250_3 (m.d 0 2) (by simp) with h264 | h264
                                  · linarith only [h2, h264, hlam]
                                  · linarith only [h234, h264, hlam]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  rcases p250_3 (m.d 0 2) (by simp) with h267 | h267
                                  · linarith only [h2, h267, hlam]
                                  · linarith only [h235, h267, hlam]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h234, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h240, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h244, hlam, p250_1]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h246, hlam, p250_1]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h235, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h241, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h245, hlam, p250_1]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h0, h241, h244, hc34, hlam, hphi, ht0b, ht45, ht5b, p250_1, u0elo1]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [hlam, p250_0]
                          · linarith only [h2, h245, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h2, h240, h244, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h237, h242, h243, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h2, h236, h238, h240, h242, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h235, h240, h241, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h2, h234, h240, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h2, h235, h237, hlam]
          · linarith only [h2, h234, h236, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h288 | h288
          · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
            · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
              · linarith only [h0, h2, h290, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h292 | h292
                · rcases m.htr 1 2 5 (by decide) (by decide) with h293 | h293
                  · linarith only [h0, h235, h293, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h296 | h296
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h297 | h297
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h298 | h298
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h299 | h299
                            · linarith only [h0, h235, h292, h298, h299, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h301 | h301
                              · linarith only [h0, h235, h292, h297, h299, h301, hlam]
                              · rcases h2bigk with h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h235, h298, hc12, hlam, hphi, ht23, p303_1, u3elo2]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h2, hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h235, h297, h298, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p303_1, u3elo2]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h235, hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h0, hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h290, hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h0, h297, hc34, hlam, hphi, ht0b, ht45, ht5b, p303_1, u0elo0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h293, hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p303_1, u3elo2]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p303_1, u3elo2]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  rcases p303_3 (m.d 0 2) (by simp) with h317 | h317
                                  · linarith only [h2, h317, hlam]
                                  · linarith only [h234, h317, hlam]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h0, h235, h292, h297, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p303_1, u3elo2]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h234, hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h292, hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h297, hlam, p303_1]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [hlam, p303_0]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h299, hlam, p303_1]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h0, h292, h297, h299, hc34, hc45, hlam, hphi, p303_1]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h292, h297, h299, hc34, hc45, hlam, hphi, p303_1]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [h298, hlam, p303_1]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  rcases p303_3 (m.d 0 2) (by simp) with h329 | h329
                                  · linarith only [h235, h329, hlam]
                                  · linarith only [h234, h329, hlam]
                                · have p303_0 := h303c.1
                                  have p303_1 := h303c.2.1
                                  have p303_2 := h303c.2.2.1
                                  have p303_3 := h303c.2.2.2
                                  linarith only [hlam, p303_0]
                          · linarith only [h0, h2, h292, h297, h298, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h2, h292, h297, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h289, h295, h296, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h2, h288, h290, h292, h295, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h2, h234, h292, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h338 | h338
              · linarith only [h0, h2, h289, h338, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h340 | h340
                · rcases m.htr 1 2 5 (by decide) (by decide) with h341 | h341
                  · linarith only [h235, h338, h341, hc02, hlam, hphi, ht23, u3elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h343 | h343
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h344 | h344
                      · linarith only [h1, h289, h344, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h346 | h346
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h347 | h347
                          · linarith only [h289, h347, hc03, hlam, hphi, u3elo2]
                          · linarith only [h0, h2, h340, h346, h347, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h2, h340, h346, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h288, h289, h343, hc13, hlam, hphi, u3elo4]
                · linarith only [h2, h234, h289, h340, hc12, hlam, hphi, ht23, u3elo4]
          · linarith only [h2, h234, h288, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h354 | h354
        · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
          · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
            · rcases m.htr 1 2 3 (by decide) (by decide) with h357 | h357
              · linarith only [h0, h2, h357, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h359 | h359
                · linarith only [h234, h357, h359, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h361 | h361
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h363 | h363
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h366 | h366
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
                              · linarith only [h1, h362, h367, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h0, h234, h361, h364, h366, h367, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h0, h234, h361, h366, hlam]
                          · linarith only [h234, h364, h365, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h2, h364, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h356, h359, h361, h362, h363, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h2, h355, h362, hc13, hlam, hphi, u3elo2]
                  · linarith only [h2, h354, h361, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h234, h354, h355, h356, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h377 | h377
            · rcases m.htr 1 2 3 (by decide) (by decide) with h378 | h378
              · linarith only [h0, h2, h378, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h380 | h380
                · linarith only [h0, h234, h380, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h382 | h382
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h383 | h383
                    · linarith only [h1, h355, h383, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h385 | h385
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                        · linarith only [h0, h2, h355, h382, h386, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · linarith only [h0, h2, h382, h386, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h377, h385, hc13, hlam, hphi, u3elo0]
                  · linarith only [h2, h354, h382, hc12, hc23, hlam, hphi]
            · linarith only [h2, h354, h377, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h392 | h392
          · rcases m.htr 0 3 5 (by decide) (by decide) with h393 | h393
            · rcases m.htr 1 2 3 (by decide) (by decide) with h394 | h394
              · linarith only [h0, h2, h394, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h396 | h396
                · linarith only [h234, h394, h396, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
                  · linarith only [h0, h354, h398, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h400 | h400
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h401 | h401
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h402 | h402
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h403 | h403
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h404 | h404
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h405 | h405
                              · linarith only [h1, h400, h405, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases h2bigk with h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h354, hc12, hc25, hlam, hphi, p407_1]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h2, hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h234, hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h354, hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h0, hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h394, hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h396, hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h398, hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p407_1, u3elo2]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p407_1, u3elo2]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h404, h405, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p407_1, u3elo2]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h0, h354, hc12, hlam, hphi, ht23, p407_1, u3elo2]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h0, h402, hc12, hlam, hphi, ht23, p407_1, u3elo2]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h402, hc12, hlam, hphi, ht23, p407_1, u3elo2]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h402, hlam, p407_1]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h0, h354, h402, hc12, hlam, hphi, ht23, p407_1, u3elo2]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h0, h403, hc12, hlam, hphi, ht23, p407_1, u3elo2]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h403, hc12, hlam, hphi, ht23, p407_1, u3elo2]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h403, hlam, p407_1]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [h404, hlam, p407_0]
                                · have p407_0 := h407c.1
                                  have p407_1 := h407c.2.1
                                  have p407_2 := h407c.2.2.1
                                  have p407_3 := h407c.2.2.2
                                  linarith only [hlam, p407_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                              · linarith only [h0, h234, h404, h433, hc12, hlam, hphi, ht23, u3elo3]
                              · rcases h2bigk with h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h234, hc12, hc24, hlam, hphi, p435_1]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h2, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h234, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h354, hlam, p435_0]
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
                                  linarith only [h394, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h396, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h398, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p435_1, u3elo2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p435_1, u3elo2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h0, h234, hc12, hlam, hphi, ht23, p435_1, u3elo2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h0, h354, hc12, hlam, hphi, ht23, p435_1, u3elo2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h0, h402, hc12, hlam, hphi, ht23, p435_1, u3elo2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h402, hc12, hlam, hphi, ht23, p435_1, u3elo2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h402, hlam, p435_1]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h404, hlam, p435_1]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h0, h403, hc12, hlam, hphi, ht23, p435_1, u3elo2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h403, hc12, hlam, hphi, ht23, p435_1, u3elo2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h403, hlam, p435_1]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h0, h234, h403, hc12, hlam, hphi, ht23, p435_1, u3elo2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hlam, p435_0]
                          · linarith only [h1, h401, h403, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h2, h402, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h2, h393, h401, hc13, hlam, hphi, u3elo2]
                    · linarith only [h2, h392, h394, h400, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h465 | h465
              · linarith only [h0, h2, h465, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h467 | h467
                · linarith only [h234, h465, h467, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h469 | h469
                  · linarith only [h0, h354, h469, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h471 | h471
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h472 | h472
                      · linarith only [h1, h393, h472, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h474 | h474
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h475 | h475
                          · linarith only [h1, h393, h471, h475, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h2, h475, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h1, h2, h471, h474, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h392, h393, h471, hc13, hlam, hphi, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h480 | h480
            · rcases m.htr 1 2 3 (by decide) (by decide) with h481 | h481
              · linarith only [h0, h2, h481, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h483 | h483
                · linarith only [h0, h234, h483, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h485 | h485
                  · linarith only [h0, h354, h485, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h487 | h487
                    · linarith only [h1, h392, h487, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h489 | h489
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                        · linarith only [h354, h392, h480, h490, hc02, hlam, hphi, ht23, u3elo2]
                        · linarith only [h0, h2, h490, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h480, h489, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h494 | h494
              · linarith only [h0, h2, h494, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h496 | h496
                · linarith only [h234, h494, h496, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h498 | h498
                  · linarith only [h0, h354, h498, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h500 | h500
                    · linarith only [h1, h392, h500, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h502 | h502
                      · linarith only [h1, h480, h502, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h504 | h504
                        · linarith only [h392, h504, hc03, hlam, hphi, u3elo2]
                        · linarith only [h0, h2, h504, hc12, hlam, hphi, ht23, u3elo3]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
