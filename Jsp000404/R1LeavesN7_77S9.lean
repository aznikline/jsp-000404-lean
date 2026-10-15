import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h6, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h8, h9, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h14, h2, h4, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                      · linarith only [h16, h2, h8, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h14, h18, h6, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                          · rcases h3bigk with h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              rcases p21_3 (m.d 0 3) (by simp) with h23 | h23
                              · rcases p21_3 (m.d 1 3) (by simp) with h24 | h24
                                · linarith only [h1, h24, hlam]
                                · rcases p21_3 (m.d 2 3) (by simp) with h26 | h26
                                  · linarith only [h2, h26, hlam]
                                  · rcases p21_3 (m.d 3 4) (by simp) with h28 | h28
                                    · linarith only [h28, h4, hlam]
                                    · linarith only [h28, h8, hlam]
                              · linarith only [h1, h23, hlam]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              rcases p21_3 (m.d 0 3) (by simp) with h32 | h32
                              · rcases p21_3 (m.d 1 3) (by simp) with h33 | h33
                                · linarith only [h1, h33, hlam]
                                · linarith only [h33, h6, hlam]
                              · linarith only [h2, h32, hlam]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h14, h2, h20, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h14, h2, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h1, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h14, h20, hc23, hc34, hlam, hphi, p21_1]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h8, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h14, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h2, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h6, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h16, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h18, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h4, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h2, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h14, h2, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h5, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h6, hc23, hlam, hphi, ht34, ht45, p21_1, u5elo3]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h20, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [hlam, p21_0]
                          · linarith only [h20, h6, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h3, h7, hc12, hlam, hphi, u2elo0]
              · linarith only [h2, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h63 | h63
            · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
              · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
                  · linarith only [h1, h4, h63, h66, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                      · linarith only [h1, h4, h64, h68, h69, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                        · linarith only [h0, h64, h71, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1, h4, h68, h71, hc23, hc34, hlam, hphi]
                    · linarith only [h4, h63, h68, hc13, hc34, hlam, hphi]
                · linarith only [h3, h65, hc12, hlam, hphi, u2elo0]
              · linarith only [h2, h64, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
              · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                  · linarith only [h1, h63, h79, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                    · linarith only [h1, h63, h81, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                      · linarith only [h1, h4, h77, h83, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                        · linarith only [h1, h63, h77, h85, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                          · rcases h3bigk with h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h63, hc13, hlam, hphi, ht34, ht45, p88_1, u5elo3]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h63, hc23, hlam, hphi, ht34, ht45, p88_1, u5elo3]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h4, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h63, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h1, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h79, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h81, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h2, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h77, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h83, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h85, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              rcases p88_3 (m.d 0 3) (by simp) with h104 | h104
                              · linarith only [h104, hlam, p88_0]
                              · rcases p88_3 (m.d 1 3) (by simp) with h106 | h106
                                · linarith only [h106, h79, hlam]
                                · rcases p88_3 (m.d 2 3) (by simp) with h108 | h108
                                  · linarith only [h108, h83, hlam]
                                  · rcases p88_3 (m.d 3 4) (by simp) with h110 | h110
                                    · rcases p88_3 (m.d 3 5) (by simp) with h111 | h111
                                      · linarith only [h111, h87, hlam]
                                      · linarith only [h111, h63, hlam]
                                    · linarith only [h110, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              rcases p88_3 (m.d 0 3) (by simp) with h115 | h115
                              · linarith only [h115, h4, hlam]
                              · linarith only [h1, h115, hlam]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              rcases p88_3 (m.d 0 3) (by simp) with h118 | h118
                              · linarith only [h118, h4, hlam]
                              · linarith only [h118, h2, hlam]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h63, hc03, hc34, hlam, hphi, p88_1]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h1, hc13, hlam, hphi, ht34, ht45, p88_1, u5elo3]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h77, hc23, hlam, hphi, ht34, ht45, p88_1, u5elo3]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, ht45, p88_1, u5elo3]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h87, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hlam, p88_0]
                          · linarith only [h1, h4, h77, h87, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h3, h78, hc12, hlam, hphi, u2elo0]
              · linarith only [h2, h77, hc12, hlam, hphi, u2elo0]
        · linarith only [h2, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h132 | h132
        · rcases m.htr 0 3 4 (by decide) (by decide) with h133 | h133
          · rcases m.htr 0 3 5 (by decide) (by decide) with h134 | h134
            · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
              · linarith only [h132, h135, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h141 | h141
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h142 | h142
                          · linarith only [h1, h138, h142, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases h3bigk with h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h135, h137, h141, h142, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo2]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h2, hlam, p144_1]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              rcases p144_3 (m.d 0 3) (by simp) with h148 | h148
                              · rcases p144_3 (m.d 1 3) (by simp) with h149 | h149
                                · linarith only [h1, h149, hlam]
                                · linarith only [h138, h149, hlam]
                              · linarith only [h148, hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              rcases p144_3 (m.d 0 3) (by simp) with h153 | h153
                              · rcases p144_3 (m.d 1 3) (by simp) with h154 | h154
                                · linarith only [h1, h154, hlam]
                                · linarith only [h139, h154, hlam]
                              · linarith only [h153, hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h1, hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h135, hlam, p144_1]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1, u0elo0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h1, h142, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1, u0elo0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h0, h137, h141, h142, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo2]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h135, h137, h141, h142, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo2]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              rcases p144_3 (m.d 0 3) (by simp) with h166 | h166
                              · linarith only [h166, h2, hlam]
                              · linarith only [h133, h166, hlam]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              rcases p144_3 (m.d 0 3) (by simp) with h169 | h169
                              · linarith only [h169, h2, hlam]
                              · linarith only [h134, h169, hlam]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h133, hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h138, hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h140, hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h142, hlam, p144_1]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h134, hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h139, hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h141, hlam, p144_0]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [h0, h137, h141, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1, u0elo1]
                            · have p144_0 := h144c.1
                              have p144_1 := h144c.2.1
                              have p144_2 := h144c.2.2.1
                              have p144_3 := h144c.2.2.2
                              linarith only [hlam, p144_0]
                        · linarith only [h141, h2, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h133, h137, h140, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h138, h139, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h133, h135, h137, h138, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h132, h137, h2, hc12, hlam, hphi, u2elo2]
            · linarith only [h133, h134, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h188 | h188
            · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
              · linarith only [h189, h2, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h191 | h191
                · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                  · linarith only [h0, h1, h133, h191, h192, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                      · linarith only [h0, h133, h191, h195, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h197 | h197
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h198 | h198
                          · rcases h3bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h195, h2, hc13, hc34, hlam, hphi, p199_1]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h2, hlam, p199_1]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h133, hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              rcases p199_3 (m.d 0 3) (by simp) with h204 | h204
                              · rcases p199_3 (m.d 1 3) (by simp) with h205 | h205
                                · linarith only [h1, h205, hlam]
                                · linarith only [h194, h205, hlam]
                              · linarith only [h204, hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h1, hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h189, hlam, p199_1]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h192, hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h1, h198, hc45, hlam, hphi, ht0b, ht5b, p199_1, u0elo0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h195, hc03, hc34, hlam, hphi, p199_1]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h195, hc13, hc34, hlam, hphi, p199_1]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h195, hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              rcases p199_3 (m.d 0 3) (by simp) with h218 | h218
                              · linarith only [h2, h218, hlam]
                              · linarith only [h188, h218, hlam]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              rcases p199_3 (m.d 0 3) (by simp) with h221 | h221
                              · linarith only [h221, hlam, p199_0]
                              · rcases p199_3 (m.d 1 3) (by simp) with h223 | h223
                                · linarith only [h192, h223, hlam]
                                · rcases p199_3 (m.d 2 3) (by simp) with h225 | h225
                                  · linarith only [h195, h225, hlam]
                                  · linarith only [h2, h225, hlam]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              rcases p199_3 (m.d 0 3) (by simp) with h228 | h228
                              · linarith only [h133, h228, hlam]
                              · linarith only [h1, h228, hlam]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h0, h191, h197, h198, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p199_1]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h0, h191, h195, h197, h2, hlam, p199_2]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h188, hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h194, hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h197, hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [h198, hlam, p199_0]
                            · have p199_0 := h199c.1
                              have p199_1 := h199c.2.1
                              have p199_2 := h199c.2.2.1
                              have p199_3 := h199c.2.2.2
                              linarith only [hlam, p199_0]
                          · linarith only [h195, h198, h2, hc02, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h191, h197, h2, hc25, hlam, hphi, u5elo3]
                    · linarith only [h188, h189, h191, h194, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h132, h191, h2, hc12, hlam, hphi, u2elo2]
            · linarith only [h132, h188, h2, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h244 | h244
          · rcases m.htr 0 3 5 (by decide) (by decide) with h245 | h245
            · rcases m.htr 1 2 3 (by decide) (by decide) with h246 | h246
              · linarith only [h0, h132, h246, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h248 | h248
                · linarith only [h0, h132, h248, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h251 | h251
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h252 | h252
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h253 | h253
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h254 | h254
                          · linarith only [h1, h250, h254, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases h3bigk with h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h2, h251, h254, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p256_1, u2elo2]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h2, hlam, p256_1]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              rcases p256_3 (m.d 0 3) (by simp) with h260 | h260
                              · rcases p256_3 (m.d 1 3) (by simp) with h261 | h261
                                · linarith only [h1, h261, hlam]
                                · linarith only [h250, h261, hlam]
                              · linarith only [h260, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              rcases p256_3 (m.d 0 3) (by simp) with h265 | h265
                              · rcases p256_3 (m.d 1 3) (by simp) with h266 | h266
                                · linarith only [h1, h266, hlam]
                                · linarith only [h251, h266, hlam]
                              · linarith only [h265, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h1, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h246, hlam, p256_1]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p256_1, u0elo0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h1, h254, hc34, hlam, hphi, ht0b, ht45, ht5b, p256_1, u0elo0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h2, hc02, hlam, hphi, p256_1, u2elo2]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h246, hc12, hlam, hphi, p256_1, u2elo2]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              rcases p256_3 (m.d 0 3) (by simp) with h278 | h278
                              · linarith only [h2, h278, hlam]
                              · linarith only [h244, h278, hlam]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              rcases p256_3 (m.d 0 3) (by simp) with h281 | h281
                              · linarith only [h2, h281, hlam]
                              · linarith only [h245, h281, hlam]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h244, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h250, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h252, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h254, hlam, p256_1]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h245, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h251, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h253, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h1, h251, hc34, hlam, hphi, ht0b, ht45, ht5b, p256_1, u0elo2]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [hlam, p256_0]
                        · linarith only [h1, h2, h251, h253, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h2, h244, h252, hlam]
                    · linarith only [h250, h251, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h2, h244, h246, h250, hc12, hlam, hphi, u2elo2]
            · linarith only [h244, h245, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h299 | h299
            · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
              · linarith only [h0, h2, h300, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h302 | h302
                · linarith only [h0, h132, h302, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h304 | h304
                  · linarith only [h1, h244, h304, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h306 | h306
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h307 | h307
                      · linarith only [h0, h2, h244, h307, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                          · rcases h3bigk with h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h306, h310, hc45, hlam, hphi, ht0b, ht5b, p311_1, u0elo2]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h2, hlam, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h244, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              rcases p311_3 (m.d 0 3) (by simp) with h316 | h316
                              · rcases p311_3 (m.d 1 3) (by simp) with h317 | h317
                                · linarith only [h1, h317, hlam]
                                · linarith only [h306, h317, hlam]
                              · linarith only [h316, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h1, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h300, hlam, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h304, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h1, h310, hc45, hlam, hphi, ht0b, ht5b, p311_1, u0elo0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h307, hc03, hc34, hlam, hphi, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h307, hc13, hc34, hlam, hphi, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h307, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              rcases p311_3 (m.d 0 3) (by simp) with h330 | h330
                              · linarith only [h2, h330, hlam]
                              · linarith only [h299, h330, hlam]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              rcases p311_3 (m.d 0 3) (by simp) with h333 | h333
                              · linarith only [h333, hlam, p311_0]
                              · rcases p311_3 (m.d 1 3) (by simp) with h335 | h335
                                · linarith only [h304, h335, hlam]
                                · rcases p311_3 (m.d 2 3) (by simp) with h337 | h337
                                  · linarith only [h307, h337, hlam]
                                  · linarith only [h2, h337, hlam]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              rcases p311_3 (m.d 0 3) (by simp) with h340 | h340
                              · linarith only [h244, h340, hlam]
                              · linarith only [h1, h340, hlam]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h0, h2, hc12, hc34, hlam, hphi, ht23, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              rcases p311_3 (m.d 0 3) (by simp) with h345 | h345
                              · linarith only [h244, h345, hlam]
                              · linarith only [h299, h345, hlam]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h299, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h306, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h309, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h310, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hlam, p311_0]
                          · linarith only [h244, h310, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h1, h2, h306, h309, hlam]
                    · linarith only [h244, h299, h306, hc13, hc34, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h356 | h356
              · linarith only [h0, h2, h356, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h358 | h358
                · linarith only [h0, h2, h299, h358, hc25, hlam, hphi, u5elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h360 | h360
                  · linarith only [h1, h299, h360, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h362 | h362
                    · linarith only [h1, h299, h362, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                      · linarith only [h2, h244, h364, hc02, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h366 | h366
                        · linarith only [h0, h2, h299, h366, hc12, hlam, hphi, u2elo2]
                        · linarith only [h0, h2, h366, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h369 | h369
      · linarith only [h0, h1, h369, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h371 | h371
        · rcases m.htr 0 3 4 (by decide) (by decide) with h372 | h372
          · rcases m.htr 0 3 5 (by decide) (by decide) with h373 | h373
            · rcases m.htr 1 2 3 (by decide) (by decide) with h374 | h374
              · linarith only [h369, h374, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1, h374, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h373, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h378 | h378
            · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
              · linarith only [h0, h1, h372, h379, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h379, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h378, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h383 | h383
          · rcases m.htr 0 3 5 (by decide) (by decide) with h384 | h384
            · rcases m.htr 1 2 3 (by decide) (by decide) with h385 | h385
              · linarith only [h0, h371, h385, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · linarith only [h0, h1, h385, hc12, hlam, hphi, u2elo2]
            · linarith only [h383, h384, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h389 | h389
            · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
              · linarith only [h0, h1, h383, h390, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h390, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h389, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h394 | h394
    · rcases m.htr 0 2 3 (by decide) (by decide) with h395 | h395
      · rcases m.htr 0 2 5 (by decide) (by decide) with h396 | h396
        · rcases m.htr 0 3 4 (by decide) (by decide) with h397 | h397
          · rcases m.htr 0 3 5 (by decide) (by decide) with h398 | h398
            · rcases m.htr 1 2 3 (by decide) (by decide) with h399 | h399
              · rcases m.htr 1 2 5 (by decide) (by decide) with h400 | h400
                · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
                  · linarith only [h0, h394, h401, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h394, h397, h399, h401, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h396, h400, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h394, h399, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h397, h398, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h407 | h407
            · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
              · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
                · rcases m.htr 1 3 4 (by decide) (by decide) with h410 | h410
                  · linarith only [h394, h397, h407, h410, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h412 | h412
                    · linarith only [h0, h394, h412, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h397, h407, h412, hc13, hc34, hlam, hphi]
                · linarith only [h0, h394, h396, h407, h409, hlam]
              · linarith only [h0, h408, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
              · rcases m.htr 1 2 5 (by decide) (by decide) with h418 | h418
                · rcases m.htr 1 3 4 (by decide) (by decide) with h419 | h419
                  · linarith only [h0, h394, h419, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h421 | h421
                    · linarith only [h0, h394, h407, h421, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h423 | h423
                      · linarith only [h394, h397, h417, h423, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h425 | h425
                        · linarith only [h394, h407, h417, h425, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h427 | h427
                          · rcases h3bigk with h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h407, h417, h427, hc23, hc34, hlam, hphi, p428_1]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h0, h394, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p428_1, u2elo1]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h397, hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h407, hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h394, hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h0, h394, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p428_1, u2elo1]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h419, hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h421, hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h395, hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h417, hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h423, hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h425, hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              rcases p428_3 (m.d 0 3) (by simp) with h444 | h444
                              · linarith only [h444, hlam, p428_0]
                              · rcases p428_3 (m.d 1 3) (by simp) with h446 | h446
                                · linarith only [h419, h446, hlam]
                                · rcases p428_3 (m.d 2 3) (by simp) with h448 | h448
                                  · linarith only [h423, h448, hlam]
                                  · rcases p428_3 (m.d 3 4) (by simp) with h450 | h450
                                    · rcases p428_3 (m.d 3 5) (by simp) with h451 | h451
                                      · linarith only [h427, h451, hlam]
                                      · linarith only [h407, h451, hlam]
                                    · linarith only [h450, hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              rcases p428_3 (m.d 0 3) (by simp) with h455 | h455
                              · linarith only [h397, h455, hlam]
                              · linarith only [h394, h455, hlam]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              rcases p428_3 (m.d 0 3) (by simp) with h458 | h458
                              · linarith only [h397, h458, hlam]
                              · linarith only [h395, h458, hlam]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [hlam, p428_0]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h407, hc03, hc34, hlam, hphi, p428_1]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [hc03, hlam, hphi, ht34, ht45, p428_1, u5elo3]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [h417, hc23, hlam, hphi, ht34, ht45, p428_1, u5elo3]
                            · have p428_0 := h428c.1
                              have p428_1 := h428c.2.1
                              have p428_2 := h428c.2.2.1
                              have p428_3 := h428c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, ht45, p428_1, u5elo3]
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
                          · linarith only [h394, h397, h417, h427, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h396, h418, hlam]
              · linarith only [h0, h394, h417, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h394, h396, hc13, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h0, h394, h395, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h473 | h473
      · rcases m.htr 0 2 5 (by decide) (by decide) with h474 | h474
        · rcases m.htr 0 3 4 (by decide) (by decide) with h475 | h475
          · rcases m.htr 0 3 5 (by decide) (by decide) with h476 | h476
            · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
              · rcases m.htr 1 2 5 (by decide) (by decide) with h478 | h478
                · rcases m.htr 1 3 4 (by decide) (by decide) with h479 | h479
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h480 | h480
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h481 | h481
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h482 | h482
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h483 | h483
                          · linarith only [h473, h481, h483, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases h3bigk with h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h394, hlam, p485_1]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h482, h483, hc34, hlam, hphi, ht0b, ht45, ht5b, p485_1, u0elo2]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              rcases p485_3 (m.d 0 3) (by simp) with h489 | h489
                              · rcases p485_3 (m.d 1 3) (by simp) with h490 | h490
                                · rcases p485_3 (m.d 2 3) (by simp) with h491 | h491
                                  · linarith only [h473, h491, hlam]
                                  · linarith only [h481, h491, hlam]
                                · linarith only [h479, h490, hlam]
                              · linarith only [h489, hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              rcases p485_3 (m.d 0 3) (by simp) with h496 | h496
                              · rcases p485_3 (m.d 1 3) (by simp) with h497 | h497
                                · rcases p485_3 (m.d 2 3) (by simp) with h498 | h498
                                  · linarith only [h473, h498, hlam]
                                  · linarith only [h482, h498, hlam]
                                · linarith only [h480, h497, hlam]
                              · linarith only [h496, hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h394, h477, hc01, hlam, hphi, ht12, p485_1, u2elo1]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h477, h482, h483, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p485_1, u2elo1]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              rcases p485_3 (m.d 0 3) (by simp) with h506 | h506
                              · linarith only [h394, h506, hlam]
                              · linarith only [h475, h506, hlam]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              rcases p485_3 (m.d 0 3) (by simp) with h509 | h509
                              · linarith only [h394, h509, hlam]
                              · linarith only [h476, h509, hlam]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h473, hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h477, hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h473, hc34, hlam, hphi, ht0b, ht45, ht5b, p485_1, u0elo1]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h0, h473, h483, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p485_1, u2elo1]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h475, hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h479, hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h481, hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h483, hlam, p485_1]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h476, hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h480, hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [h482, hlam, p485_0]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [hc34, hlam, hphi, ht45, p485_1, u5elo3]
                            · have p485_0 := h485c.1
                              have p485_1 := h485c.2.1
                              have p485_2 := h485c.2.2.1
                              have p485_3 := h485c.2.2.2
                              linarith only [hlam, p485_0]
                        · linarith only [h394, h476, h477, h481, h482, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h528 | h528
                        · linarith only [h394, h475, h477, h481, h528, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h530 | h530
                          · rcases h3bigk with h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h394, hlam, p531_1]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              rcases p531_3 (m.d 0 3) (by simp) with h534 | h534
                              · rcases p531_3 (m.d 1 3) (by simp) with h535 | h535
                                · rcases p531_3 (m.d 2 3) (by simp) with h536 | h536
                                  · linarith only [h473, h536, hlam]
                                  · rcases p531_3 (m.d 3 4) (by simp) with h538 | h538
                                    · linarith only [h475, h538, hlam]
                                    · linarith only [h481, h538, hlam]
                                · linarith only [h477, h535, hlam]
                              · linarith only [h473, h534, hlam]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h394, h477, h528, h530, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p531_1, u2elo1]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h394, h477, h528, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p531_1, u2elo1]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h394, h477, hc01, hlam, hphi, ht12, p531_1, u2elo1]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              rcases p531_3 (m.d 0 3) (by simp) with h547 | h547
                              · linarith only [h394, h547, hlam]
                              · linarith only [h473, h547, hlam]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h477, h528, h530, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p531_1, u2elo1]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h477, h528, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p531_1, u2elo1]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h473, hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h477, hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h481, hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h528, hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h475, hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h479, hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h473, h475, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p531_1, u0elo1]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h0, h473, h475, h528, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p531_1, u2elo1]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h476, hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h480, hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h480, hc23, hlam, hphi, ht34, ht45, p531_1, u5elo1]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [h530, hlam, p531_0]
                            · have p531_0 := h531c.1
                              have p531_1 := h531c.2.1
                              have p531_2 := h531c.2.2.1
                              have p531_3 := h531c.2.2.2
                              linarith only [hlam, p531_0]
                          · linarith only [h481, h530, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h394, h473, h476, h480, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h394, h475, h479, hlam]
                · linarith only [h0, h473, h475, h478, hc34, hlam, hphi, ht45, u5elo2]
              · linarith only [h0, h477, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h475, h476, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h573 | h573
            · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
              · rcases m.htr 1 2 5 (by decide) (by decide) with h575 | h575
                · rcases m.htr 1 3 4 (by decide) (by decide) with h576 | h576
                  · linarith only [h475, h573, h574, h576, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h578 | h578
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h579 | h579
                      · linarith only [h473, h576, h579, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h581 | h581
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h582 | h582
                          · rcases h3bigk with h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h394, hlam, p583_1]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h581, h582, hc45, hlam, hphi, ht0b, ht5b, p583_1, u0elo2]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h475, hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              rcases p583_3 (m.d 0 3) (by simp) with h588 | h588
                              · rcases p583_3 (m.d 1 3) (by simp) with h589 | h589
                                · rcases p583_3 (m.d 2 3) (by simp) with h590 | h590
                                  · linarith only [h473, h590, hlam]
                                  · linarith only [h581, h590, hlam]
                                · linarith only [h578, h589, hlam]
                              · linarith only [h588, hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h576, hc03, hc34, hlam, hphi, p583_1]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h576, h581, h582, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p583_1]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h576, hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              rcases p583_3 (m.d 0 3) (by simp) with h599 | h599
                              · linarith only [h394, h599, hlam]
                              · linarith only [h573, h599, hlam]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h473, hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h574, hlam, p583_0]
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
                              linarith only [h0, h473, h582, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p583_1, u2elo1]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              rcases p583_3 (m.d 0 3) (by simp) with h607 | h607
                              · linarith only [h607, hlam, p583_0]
                              · rcases p583_3 (m.d 1 3) (by simp) with h609 | h609
                                · linarith only [h576, h609, hlam]
                                · linarith only [h394, h609, hlam]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h394, hc01, hc34, hlam, hphi, ht12, ht23, p583_1]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              rcases p583_3 (m.d 0 3) (by simp) with h613 | h613
                              · linarith only [h475, h613, hlam]
                              · linarith only [h473, h613, hlam]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              rcases p583_3 (m.d 0 3) (by simp) with h617 | h617
                              · linarith only [h475, h617, hlam]
                              · linarith only [h573, h617, hlam]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h573, hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h578, hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h581, hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [h582, hlam, p583_0]
                            · have p583_0 := h583c.1
                              have p583_1 := h583c.2.1
                              have p583_2 := h583c.2.2.1
                              have p583_3 := h583c.2.2.2
                              linarith only [hlam, p583_0]
                          · linarith only [h475, h582, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h394, h573, h576, h581, hc23, hc34, hlam, hphi]
                    · linarith only [h394, h573, h578, hlam]
                · linarith only [h0, h575, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h574, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
              · rcases m.htr 1 2 5 (by decide) (by decide) with h631 | h631
                · rcases m.htr 1 3 4 (by decide) (by decide) with h632 | h632
                  · linarith only [h394, h475, h630, h632, hc01, hlam, hphi, ht12, u2elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h634 | h634
                    · linarith only [h394, h573, h632, h634, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h394, h634, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h474, h631, hc12, hlam, hphi, u2elo0]
              · linarith only [h0, h630, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h473, h474, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h640 | h640
        · rcases m.htr 0 3 4 (by decide) (by decide) with h641 | h641
          · rcases m.htr 0 3 5 (by decide) (by decide) with h642 | h642
            · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
              · linarith only [h473, h640, h643, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h643, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h473, h640, h642, hc25, hlam, hphi, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h647 | h647
            · rcases m.htr 1 2 3 (by decide) (by decide) with h648 | h648
              · linarith only [h473, h640, h648, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h648, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h473, h640, h647, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h652 | h652
          · rcases m.htr 0 3 5 (by decide) (by decide) with h653 | h653
            · rcases m.htr 1 2 3 (by decide) (by decide) with h654 | h654
              · linarith only [h473, h654, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h654, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h652, h653, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h658 | h658
            · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
              · linarith only [h0, h473, h659, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h659, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
              · linarith only [h0, h473, h662, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h662, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
