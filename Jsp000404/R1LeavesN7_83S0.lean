import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_I_L_0_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h5, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h5, h8, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                    · linarith only [h12, h8, hc13, hlam, hphi, u3elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h0, h14, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h14, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h3, h5, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h19, h2, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
                · linarith only [h0, h2, h21, h5, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h21, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h25 | h25
          · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
            · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
              · linarith only [h0, h27, h3, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                  · linarith only [h26, h27, h30, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                    · linarith only [h0, h26, h30, h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h2, h3, h32, hc23, hlam, hphi, u3elo3]
                · linarith only [h25, h26, h29, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2, h26, h3, hc12, hc24, hlam, hphi]
          · linarith only [h25, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h38 | h38
        · rcases m.htr 0 2 5 (by decide) (by decide) with h39 | h39
          · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
            · linarith only [h0, h2, h38, h40, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
              · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                        · linarith only [h0, h2, h42, h47, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · linarith only [h45, h47, hc34, hlam, hphi, ht45, u5elo4]
                      · linarith only [h0, h2, h42, h45, h46, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h0, h2, h42, h45, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h40, h42, h44, hlam]
                · linarith only [h42, h43, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h2, h38, h42, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h39, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h56 | h56
          · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
            · linarith only [h0, h2, h57, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
              · linarith only [h0, h38, h59, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                          · rcases h2bigk with h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h38, h63, hc12, hlam, hphi, ht23, p67_1, u3elo2]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h2, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h38, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h38, h63, h64, h66, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p67_1, u3elo2]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h0, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h57, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h59, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h0, h64, h66, hc45, hlam, hphi, ht0b, ht5b, p67_1, u0elo0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hc02, hlam, hphi, ht23, p67_1, u3elo2]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, p67_1, u3elo2]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h38, h56, h64, h66, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p67_1, u3elo2]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              rcases p67_3 (m.d 0 2) (by simp) with h82 | h82
                              · linarith only [h2, h82, hlam]
                              · linarith only [h56, h82, hlam]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h0, h61, h63, h64, h66, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p67_1, u3elo2]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h61, h63, h64, h66, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p67_1, u3elo2]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h63, hlam, p67_1]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              rcases p67_3 (m.d 0 2) (by simp) with h89 | h89
                              · linarith only [h38, h89, hlam]
                              · linarith only [h56, h89, hlam]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h56, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h61, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h64, hlam, p67_1]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h65, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hlam, p67_0]
                          · linarith only [h66, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h65, hc24, hlam, hphi, ht45, u5elo4]
                      · linarith only [h2, h64, hc03, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h2, h63, hc02, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                    · linarith only [h101, h57, h61, h62, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h0, h101, h2, h61, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h2, h56, h61, hc12, hc23, hlam, hphi]
          · linarith only [h56, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h1, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h107 | h107
    · rcases m.htr 0 2 3 (by decide) (by decide) with h108 | h108
      · rcases m.htr 0 2 4 (by decide) (by decide) with h109 | h109
        · rcases m.htr 0 2 5 (by decide) (by decide) with h110 | h110
          · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
            · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
              · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h116 | h116
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h118 | h118
                          · linarith only [h108, h115, h118, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h118, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h117, hc24, hlam, hphi, ht45, u5elo4]
                      · linarith only [h116, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h114, h115, hc23, hlam, hphi, u3elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                    · linarith only [h114, h124, hc13, hlam, hphi, u3elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h128 | h128
                          · rcases h2bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h0, hlam, p129_1]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h126, h128, hc45, hlam, hphi, ht0b, ht5b, p129_1, u0elo1]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h124, h126, h128, hc45, hlam, hphi, ht0b, ht5b, p129_1, u0elo1]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              rcases p129_3 (m.d 0 2) (by simp) with h134 | h134
                              · rcases p129_3 (m.d 1 2) (by simp) with h135 | h135
                                · rcases p129_3 (m.d 2 3) (by simp) with h136 | h136
                                  · linarith only [h108, h136, hlam]
                                  · linarith only [h126, h136, hlam]
                                · linarith only [h113, h135, hlam]
                              · linarith only [h134, hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h108, h126, h128, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p129_1]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              rcases p129_3 (m.d 0 2) (by simp) with h143 | h143
                              · linarith only [h0, h143, hlam]
                              · linarith only [h108, h143, hlam]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              rcases p129_3 (m.d 0 2) (by simp) with h146 | h146
                              · linarith only [h0, h146, hlam]
                              · linarith only [h109, h146, hlam]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              rcases p129_3 (m.d 0 2) (by simp) with h149 | h149
                              · linarith only [h0, h149, hlam]
                              · linarith only [h110, h149, hlam]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h108, hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h111, hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h124, hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h111, h114, h126, h128, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p129_1, u3elo3]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h109, hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h112, hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h109, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p129_1, u0elo1]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h109, h126, h128, hc45, hlam, hphi, ht0b, ht5b, p129_1, u0elo1]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h110, hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h113, hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h126, hlam, p129_1]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [h127, hlam, p129_0]
                            · have p129_0 := h129c.1
                              have p129_1 := h129c.2.1
                              have p129_2 := h129c.2.2.1
                              have p129_3 := h129c.2.2.2
                              linarith only [hlam, p129_0]
                          · linarith only [h111, h114, h126, h128, hc35, hlam, hphi, u5elo4]
                        · linarith only [h127, hc24, hlam, hphi, ht45, u5elo4]
                      · linarith only [h126, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h113, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h107, h109, h112, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
            · linarith only [h0, h107, h111, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
          · linarith only [h110, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h174 | h174
          · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
            · rcases m.htr 1 2 4 (by decide) (by decide) with h176 | h176
              · rcases m.htr 1 2 5 (by decide) (by decide) with h177 | h177
                · rcases m.htr 1 3 4 (by decide) (by decide) with h178 | h178
                  · linarith only [h108, h109, h176, h178, hc23, hlam, hphi, u3elo1]
                  · linarith only [h108, h109, h176, h178, hc23, hlam, hphi, u3elo3]
                · linarith only [h108, h109, h176, h177, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
                  · linarith only [h175, h176, h183, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                    · linarith only [h108, h183, h185, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h107, h176, h182, h185, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h0, h107, h182, hc15, hlam, hphi, u5elo2]
            · linarith only [h0, h107, h175, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
          · linarith only [h174, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h191 | h191
        · rcases m.htr 0 2 5 (by decide) (by decide) with h192 | h192
          · rcases m.htr 1 2 3 (by decide) (by decide) with h193 | h193
            · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
              · rcases m.htr 1 2 5 (by decide) (by decide) with h195 | h195
                · rcases m.htr 1 3 4 (by decide) (by decide) with h196 | h196
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                        · linarith only [h108, h191, h193, h199, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h199, hc24, hlam, hphi, ht45, u5elo4]
                      · linarith only [h108, h198, hc02, hlam, hphi, ht23, u3elo4]
                    · linarith only [h0, h107, h108, h195, h197, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h107, h108, h193, h195, h196, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h0, h107, h108, h193, h195, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h108, h191, h193, h194, hlam]
            · linarith only [h0, h107, h193, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
          · linarith only [h0, h107, h192, hc15, hlam, hphi, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h209 | h209
          · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
            · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
              · rcases m.htr 1 2 5 (by decide) (by decide) with h212 | h212
                · rcases m.htr 1 3 4 (by decide) (by decide) with h213 | h213
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h215 | h215
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h216 | h216
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h217 | h217
                          · rcases h2bigk with h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h0, hlam, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h108, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h191, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h108, h210, h215, h217, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p218_1, u3elo1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              rcases p218_3 (m.d 0 2) (by simp) with h224 | h224
                              · linarith only [h0, h224, hlam]
                              · rcases p218_3 (m.d 1 2) (by simp) with h226 | h226
                                · rcases p218_3 (m.d 2 3) (by simp) with h227 | h227
                                  · linarith only [h210, h227, hlam]
                                  · linarith only [h108, h227, hlam]
                                · linarith only [h0, h226, hlam]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h0, h107, h108, h212, h215, h217, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h0, h107, h191, h212, h215, h217, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h0, h107, h108, h210, h212, hlam, p218_2]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h0, h107, h212, h215, h217, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p218_1, u3elo2]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h210, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h0, h107, h191, h210, h212, h215, h217, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p218_1, u3elo1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              rcases p218_3 (m.d 0 2) (by simp) with h239 | h239
                              · linarith only [h108, h239, hlam]
                              · linarith only [h209, h239, hlam]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h0, h107, h211, h212, h215, h217, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h211, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h214, hlam, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              rcases p218_3 (m.d 0 2) (by simp) with h246 | h246
                              · linarith only [h191, h246, hlam]
                              · linarith only [h209, h246, hlam]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h209, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h212, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h215, hlam, p218_1]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [h216, hlam, p218_0]
                            · have p218_0 := h218c.1
                              have p218_1 := h218c.2.1
                              have p218_2 := h218c.2.2.1
                              have p218_3 := h218c.2.2.2
                              linarith only [hlam, p218_0]
                          · linarith only [h217, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h191, h216, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h215, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h107, h108, h212, h214, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h107, h108, h210, h212, h213, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h212, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h107, h108, h210, h211, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · linarith only [h0, h107, h210, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
          · linarith only [h0, h107, h209, hc15, hlam, hphi, u5elo2]
    · linarith only [h107, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem r1l7_10_12_13_25_L_0_L_I_L_R_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h1, h4, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h1, h4, h8, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h1, h10, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h10, h12, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                  · linarith only [h12, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h1, h3, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16 | h16
        · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
          · linarith only [h0, h17, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · linarith only [h1, h17, h2, hc12, hc24, hlam, hphi]
        · linarith only [h1, h16, hlam, hphi, ht34, ht45, u3ehi0, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h21 | h21
      · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
        · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
          · linarith only [h0, h1, h21, h23, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
            · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
              · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                · linarith only [h0, h25, h27, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h0, h1, h25, h27, hlam]
              · linarith only [h25, h26, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h1, h21, h25, hc12, hc23, hlam, hphi]
        · linarith only [h21, h22, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h33 | h33
        · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
          · linarith only [h0, h34, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
            · linarith only [h0, h21, h33, h36, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
              · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                  · linarith only [h0, h38, h40, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                  · linarith only [h21, h39, h40, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                  · linarith only [h39, h43, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h43, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h1, h33, h38, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
          · linarith only [h0, h47, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
            · linarith only [h0, h21, h49, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
              · linarith only [h0, h33, h51, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h55 | h55
                    · rcases h2bigk with h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h33, hc12, hlam, hphi, ht23, ht34, ht45, p56_1, u5elo2]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h1, hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h21, hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h33, hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h0, hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h47, hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h49, hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h51, hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        rcases p56_3 (m.d 0 2) (by simp) with h67 | h67
                        · linarith only [h67, hlam, p56_0]
                        · rcases p56_3 (m.d 1 2) (by simp) with h69 | h69
                          · linarith only [h47, h69, hlam]
                          · rcases p56_3 (m.d 2 3) (by simp) with h71 | h71
                            · rcases p56_3 (m.d 2 4) (by simp) with h72 | h72
                              · linarith only [h53, h72, hlam]
                              · linarith only [h21, h72, hlam]
                            · linarith only [h71, hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        rcases p56_3 (m.d 0 2) (by simp) with h76 | h76
                        · linarith only [h1, h76, hlam]
                        · linarith only [h0, h76, hlam]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h0, h21, hc12, hc23, hlam, hphi, p56_1]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h0, h33, hc12, hc23, hlam, hphi, p56_1]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        rcases p56_3 (m.d 0 2) (by simp) with h82 | h82
                        · linarith only [h82, hlam, p56_0]
                        · rcases p56_3 (m.d 1 2) (by simp) with h84 | h84
                          · linarith only [h49, h84, hlam]
                          · rcases p56_3 (m.d 2 3) (by simp) with h86 | h86
                            · rcases p56_3 (m.d 2 4) (by simp) with h87 | h87
                              · rcases p56_3 (m.d 2 5) (by simp) with h88 | h88
                                · linarith only [h55, h88, hlam]
                                · linarith only [h33, h88, hlam]
                              · linarith only [h87, hlam, p56_0]
                            · linarith only [h1, h86, hlam]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        rcases p56_3 (m.d 0 2) (by simp) with h93 | h93
                        · linarith only [h21, h93, hlam]
                        · linarith only [h0, h93, hlam]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h53, hlam, p56_1]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h0, h33, hc12, hc24, hlam, hphi, p56_1]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p56_1, u5elo2]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p56_1, u5elo2]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h54, hlam, p56_1]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [h55, hlam, p56_0]
                      · have p56_0 := h56c.1
                        have p56_1 := h56c.2.1
                        have p56_2 := h56c.2.2.1
                        have p56_3 := h56c.2.2.2
                        linarith only [hlam, p56_0]
                    · linarith only [h0, h21, h55, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h54, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                  · linarith only [h106, h53, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h106, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h109 | h109
    · rcases m.htr 0 2 4 (by decide) (by decide) with h110 | h110
      · rcases m.htr 0 2 5 (by decide) (by decide) with h111 | h111
        · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
          · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
            · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
              · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                · linarith only [h109, h115, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h117 | h117
                  · linarith only [h110, h115, h117, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                  · linarith only [h117, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h0, h111, h114, hlam]
            · linarith only [h0, h110, h113, hlam]
          · linarith only [h0, h109, h112, hlam]
        · linarith only [h109, h111, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h124 | h124
        · rcases m.htr 1 2 3 (by decide) (by decide) with h125 | h125
          · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
            · linarith only [h109, h110, h126, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
              · rcases m.htr 2 3 4 (by decide) (by decide) with h129 | h129
                · linarith only [h109, h129, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · linarith only [h0, h109, h126, h129, hc34, hlam, hphi, u3ehi2]
              · linarith only [h0, h109, h124, h128, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi2]
          · linarith only [h0, h109, h125, hlam]
        · linarith only [h109, h124, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h135 | h135
      · rcases m.htr 0 2 5 (by decide) (by decide) with h136 | h136
        · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
          · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
            · rcases m.htr 1 2 5 (by decide) (by decide) with h139 | h139
              · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                · linarith only [h109, h135, h137, h140, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h109, h135, h140, hlam]
              · linarith only [h109, h136, h139, hc12, hc23, hlam, hphi]
            · linarith only [h109, h135, h137, h138, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
            · rcases m.htr 1 2 5 (by decide) (by decide) with h146 | h146
              · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
                · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h149 | h149
                    · rcases h2bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h0, hlam, p150_1]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h109, hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h148, h149, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u0elo1, u3ehi4]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h0, h137, h148, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p150_1, u3ehi4]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h137, hc02, hc23, hlam, hphi, p150_1]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h137, hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h137, h148, h149, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p150_1, u3ehi4]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h137, h148, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p150_1, u3ehi4]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h135, h148, h149, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p150_1, u3ehi4]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p150_1]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        rcases p150_3 (m.d 0 2) (by simp) with h164 | h164
                        · linarith only [h109, h164, hlam]
                        · linarith only [h135, h164, hlam]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        rcases p150_3 (m.d 0 2) (by simp) with h167 | h167
                        · linarith only [h109, h167, hlam]
                        · linarith only [h136, h167, hlam]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h135, hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h145, hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h147, hlam, p150_1]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h135, h148, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u0elo1, u3ehi4]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h136, hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h146, hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h148, hlam, p150_1]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [h149, hlam, p150_0]
                      · have p150_0 := h150c.1
                        have p150_1 := h150c.2.1
                        have p150_2 := h150c.2.2.1
                        have p150_3 := h150c.2.2.2
                        linarith only [hlam, p150_0]
                    · linarith only [h147, h149, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h0, h137, h148, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h137, h147, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h136, h146, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h135, h145, hlam]
        · linarith only [h135, h136, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h186 | h186
        · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
          · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
            · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
              · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                · rcases m.htr 2 3 5 (by decide) (by decide) with h191 | h191
                  · linarith only [h109, h186, h187, h191, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h0, h135, h190, h191, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                  · linarith only [h190, h194, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h109, h194, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
              · linarith only [h186, h187, h189, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
            · linarith only [h109, h186, h187, h188, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
            · linarith only [h135, h186, h187, h199, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
              · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                    · rcases h2bigk with h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h0, hlam, p205_1]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h109, hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h135, hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h203, hlam, hphi, ht0b, ht34, ht45, ht5b, p205_1, u0elo1, u3ehi4]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h199, h202, hc02, hc23, hlam, hphi, p205_1]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h187, hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h199, hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h199, h202, h203, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p205_1, u3ehi4]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h186, h203, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p205_1, u3ehi4]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p205_1]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h135, h186, h203, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p205_1, u3ehi4]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        rcases p205_3 (m.d 0 2) (by simp) with h220 | h220
                        · linarith only [h109, h220, hlam]
                        · linarith only [h186, h220, hlam]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h186, h203, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p205_1, u3ehi4]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h0, h186, h203, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p205_1, u3ehi4]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h202, hlam, p205_1]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        rcases p205_3 (m.d 0 2) (by simp) with h227 | h227
                        · linarith only [h135, h227, hlam]
                        · linarith only [h186, h227, hlam]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h186, hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h201, hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h203, hlam, p205_1]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [h204, hlam, p205_0]
                      · have p205_0 := h205c.1
                        have p205_1 := h205c.2.1
                        have p205_2 := h205c.2.2.1
                        have p205_3 := h205c.2.2.2
                        linarith only [hlam, p205_0]
                    · linarith only [h135, h186, h203, h204, hlam, hphi, ht34, ht45, u3ehi4, u5elo4]
                  · linarith only [h203, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h0, h187, h202, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h186, h201, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
          · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
            · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
              · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
                · rcases m.htr 2 3 5 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h244 | h244
                    · rcases h2bigk with h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h0, hlam, p245_1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h109, hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h135, hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h186, hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        rcases p245_3 (m.d 0 2) (by simp) with h251 | h251
                        · linarith only [h0, h251, hlam]
                        · rcases p245_3 (m.d 1 2) (by simp) with h253 | h253
                          · rcases p245_3 (m.d 2 3) (by simp) with h254 | h254
                            · linarith only [h239, h254, hlam]
                            · linarith only [h109, h254, hlam]
                          · linarith only [h0, h253, hlam]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h242, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p245_1, u3ehi3]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h0, h135, hc01, hc12, hlam, hphi, p245_1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h0, h186, hc01, hc12, hlam, hphi, p245_1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h0, h239, hc01, hc12, hlam, hphi, p245_1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h239, hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h0, h135, h239, hc01, hc12, hlam, hphi, p245_1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h0, h186, h239, hc01, hc12, hlam, hphi, p245_1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h0, h240, hc01, hc12, hlam, hphi, p245_1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h240, hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h242, hlam, p245_1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h0, h186, h239, h242, hc01, hc12, hlam, hphi, p245_1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h0, h241, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p245_1, u5elo1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h241, hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h243, hlam, p245_1]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [h244, hlam, p245_0]
                      · have p245_0 := h245c.1
                        have p245_1 := h245c.2.1
                        have p245_2 := h245c.2.2.1
                        have p245_3 := h245c.2.2.2
                        linarith only [hlam, p245_0]
                    · linarith only [h0, h135, h244, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h109, h243, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h279 | h279
                  · linarith only [h242, h279, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h279, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h0, h241, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h109, h239, h240, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h284 | h284
            · linarith only [h0, h135, h239, h284, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
              · linarith only [h0, h186, h239, h286, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h286, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem r1l7_10_12_13_25_L_I_L_0_L_0_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h2, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                    · linarith only [h8, h9, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h5, h8, hc23, hlam, hphi, u3elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h14, h7, hc13, hlam, hphi, u3elo2]
                    · linarith only [h13, h14, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h13, h5, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h2, h20, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                    · linarith only [h18, h20, hc23, hlam, hphi, u3elo1]
                  · linarith only [h19, h5, hc23, hlam, hphi, u3elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h18, h25, hc13, hlam, hphi, u3elo2]
                    · linarith only [h24, h25, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h24, h5, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                · linarith only [h1, h30, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                  · linarith only [h32, h5, hc03, hlam, hphi, u3elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h2, h30, h34, h5, hc13, hlam, hphi, u3elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                      · linarith only [h3, h36, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
                      · linarith only [h29, h32, h36, h5, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                · linarith only [h1, h29, h39, h5, hlam, hphi, u5ehi8, u5elo4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                  · linarith only [h2, h29, h41, h5, hc34, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                    · linarith only [h2, h29, h39, h43, h5, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                      · linarith only [h29, h3, h45, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                        · linarith only [h1, h29, h47, h5, hc13, hlam, hphi, u3elo3]
                        · linarith only [h1, h47, h5, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h2, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h51 | h51
          · linarith only [h3, h51, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
          · linarith only [h2, h51, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h54 | h54
        · rcases m.htr 0 2 5 (by decide) (by decide) with h55 | h55
          · linarith only [h2, h55, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
          · linarith only [h54, h55, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h58 | h58
          · linarith only [h54, h58, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h60 | h60
            · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
              · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                        · linarith only [h2, h60, h66, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi9]
                        · rcases h0bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 1) (by simp) with h70 | h70
                            · rcases p68_3 (m.d 0 2) (by simp) with h71 | h71
                              · linarith only [h0, h71, hlam]
                              · rcases p68_3 (m.d 0 3) (by simp) with h73 | h73
                                · linarith only [h1, h73, hlam]
                                · linarith only [h2, h73, hlam]
                            · linarith only [h0, h70, hlam]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h1, h62, hc01, hlam, hphi, ht0b, ht5b, p68_1, u5ehi8]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h61, h66, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 1) (by simp) with h79 | h79
                            · rcases p68_3 (m.d 0 2) (by simp) with h80 | h80
                              · linarith only [h0, h80, hlam]
                              · rcases p68_3 (m.d 0 3) (by simp) with h82 | h82
                                · linarith only [h1, h82, hlam]
                                · linarith only [h60, h61, h66, h82, hc34, hlam, hphi, ht45, u5elo0]
                            · linarith only [h79, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h2, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h54, hlam, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h58, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h1, hlam, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, p68_1, u3elo0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h2, h61, h66, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p68_1, u3elo2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p68_1, u3elo2, u5ehi5]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h1, h62, hc04, hlam, hphi, ht0b, ht5b, p68_1, u5ehi8]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h54, h63, hc12, hlam, hphi, ht23, p68_1, u3elo2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h60, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h54, h61, h63, h66, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p68_1, u3elo2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h1, h62, hc05, hlam, hphi, ht0b, ht5b, p68_1, u5ehi8]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h58, hc12, hlam, hphi, ht23, ht34, ht45, p68_1, u5elo2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h54, h58, h61, h63, h66, hc03, hc34, hlam, hphi, ht45, p68_1, u3elo2, u5elo2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h61, hlam, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                      · linarith only [h0, h54, h60, h61, h65, hc12, hlam, hphi, ht23, u3elo0]
                    · linarith only [h2, h60, h61, h64, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi9]
                  · linarith only [h2, h60, h61, h63, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi9]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                    · linarith only [h110, h62, hc13, hlam, hphi, u3elo2]
                    · linarith only [h0, h110, h2, hc12, hlam, hphi, ht23, u3elo4]
                  · linarith only [h109, h2, h60, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h116 | h116
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                      · linarith only [h0, h117, h54, h61, hc12, hlam, hphi, u2elo3]
                      · linarith only [h0, h1, h114, h117, h2, h54, hc12, hlam, hphi, ht23, u3elo2, u5ehi8, u5elo4]
                    · linarith only [h1, h114, h116, h2, hlam]
                  · linarith only [h1, h114, h115, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                    · linarith only [h114, h123, hc13, hlam, hphi, u3elo2]
                    · linarith only [h0, h123, h2, hc12, hlam, hphi, ht23, u3elo4]
                  · linarith only [h0, h122, h2, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h127 | h127
              · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                · linarith only [h1, h128, h60, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                  · linarith only [h130, h60, hc03, hlam, hphi, u3elo2]
                  · linarith only [h0, h130, h2, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                · linarith only [h1, h127, h133, h60, hlam, hphi, u5ehi8, u5elo4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                  · linarith only [h0, h135, h2, h60, hc12, hlam, hphi, u2elo2]
                  · linarith only [h0, h135, h2, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h139 | h139
    · rcases m.htr 0 2 3 (by decide) (by decide) with h140 | h140
      · rcases m.htr 0 2 4 (by decide) (by decide) with h141 | h141
        · rcases m.htr 0 2 5 (by decide) (by decide) with h142 | h142
          · rcases m.htr 0 3 4 (by decide) (by decide) with h143 | h143
            · rcases m.htr 0 4 5 (by decide) (by decide) with h144 | h144
              · linarith only [h0, h139, h143, h144, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                · linarith only [h0, h139, h146, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                    · linarith only [h140, h146, h149, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h148, h149, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h0, h139, h143, h148, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h153 | h153
              · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
                · linarith only [h0, h139, h154, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                  · linarith only [h143, h156, hc03, hlam, hphi, u3elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                    · linarith only [h0, h139, h140, h154, h158, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                      · linarith only [h0, h141, h160, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
                      · linarith only [h143, h153, h156, h160, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
                · linarith only [h0, h139, h163, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                  · linarith only [h140, h143, h153, h165, hc34, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h167 | h167
                    · linarith only [h140, h143, h153, h163, h167, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h169 | h169
                      · linarith only [h0, h141, h143, h153, h169, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h171 | h171
                        · linarith only [h139, h143, h153, h171, hc13, hlam, hphi, u3elo3]
                        · linarith only [h139, h143, h171, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h0, h139, h142, hc13, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h175 | h175
          · linarith only [h141, h175, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
          · linarith only [h0, h139, h175, hc13, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h0, h139, h140, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h179 | h179
      · rcases m.htr 0 2 4 (by decide) (by decide) with h180 | h180
        · rcases m.htr 0 2 5 (by decide) (by decide) with h181 | h181
          · rcases m.htr 0 3 4 (by decide) (by decide) with h182 | h182
            · rcases m.htr 0 4 5 (by decide) (by decide) with h183 | h183
              · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                    · linarith only [h179, h186, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                    · linarith only [h184, h185, h186, hc34, hlam, hphi, ht45, u5elo1]
                  · linarith only [h182, h185, hc23, hlam, hphi, u3elo0]
                · linarith only [h139, h182, h184, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h191 | h191
                · rcases m.htr 2 3 4 (by decide) (by decide) with h192 | h192
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h193 | h193
                    · linarith only [h0, h179, h193, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                    · linarith only [h191, h193, hc23, hlam, hphi, u3elo1]
                  · linarith only [h139, h182, h192, hc23, hlam, hphi, u3elo1]
                · linarith only [h139, h191, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h198 | h198
              · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                  · linarith only [h182, h200, hc03, hlam, hphi, u3elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                    · linarith only [h0, h179, h202, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                    · linarith only [h199, h202, hc23, hlam, hphi, u3elo1]
                · linarith only [h139, h199, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h206 | h206
                · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                  · linarith only [h179, h182, h198, h207, hc34, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
                    · linarith only [h179, h182, h198, h209, hlam, hphi, u5ehi8, u5elo4]
                    · linarith only [h206, h209, hc23, hlam, hphi, u3elo1]
                · linarith only [h139, h206, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h179, h181, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h214 | h214
          · linarith only [h180, h214, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
          · linarith only [h179, h214, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h217 | h217
        · rcases m.htr 0 2 5 (by decide) (by decide) with h218 | h218
          · linarith only [h179, h218, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
          · linarith only [h217, h218, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h221 | h221
          · linarith only [h217, h221, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h223 | h223
            · rcases m.htr 0 4 5 (by decide) (by decide) with h224 | h224
              · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                        · linarith only [h139, h223, h229, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi9]
                        · rcases h0bigk with h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h0, hlam, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h139, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h224, h229, hc01, hlam, hphi, ht0b, ht5b, p231_1, u5ehi8]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h0, h221, hlam, hphi, p231_1, u5ehi5, u5elo2]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h221, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p231_1, u5elo2]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h179, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h217, hlam, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h221, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h139, hc01, hlam, hphi, ht12, ht23, p231_1, u3elo1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h139, hc02, hlam, hphi, ht23, p231_1, u3elo1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h139, h224, h229, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p231_1, u3elo1, u5ehi8]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h139, h224, h229, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p231_1, u3elo1, u5ehi8]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h217, h226, hc01, hlam, hphi, ht12, ht23, p231_1, u3elo2]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h0, h217, h226, hc01, hlam, hphi, ht12, ht23, p231_1, u3elo2]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h223, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h217, h224, h226, h229, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p231_1, u3elo2, u5ehi8]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p231_1, u5elo0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h0, h221, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p231_1, u5elo2]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h217, h221, h224, h226, h229, hc03, hlam, hphi, p231_1, u3elo2, u5ehi8, u5elo2]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h224, hlam, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                      · linarith only [h217, h224, h228, hlam]
                    · linarith only [h217, h224, h226, h227, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi9]
                  · linarith only [h179, h223, h224, h226, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi9]
                · linarith only [h139, h225, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h261 | h261
                · rcases m.htr 2 3 4 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h263 | h263
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h264 | h264
                      · linarith only [h0, h217, h224, h262, h264, hc01, hlam, hphi, ht12, ht23, u3elo2]
                      · linarith only [h0, h217, h264, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h179, h261, h263, hc03, hlam, hphi, u3elo1]
                  · linarith only [h0, h179, h262, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h139, h261, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h270 | h270
              · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                  · linarith only [h223, h272, hc03, hlam, hphi, u3elo2]
                  · linarith only [h0, h179, h272, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h139, h271, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h276 | h276
                · rcases m.htr 2 3 4 (by decide) (by decide) with h277 | h277
                  · linarith only [h0, h179, h223, h277, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h0, h179, h277, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h139, h276, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]

end R2N4
