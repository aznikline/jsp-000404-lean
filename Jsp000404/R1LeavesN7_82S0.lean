import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_I_L_0_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
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
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                    · linarith only [h7, h9, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h0, h2, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h1, h13, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h0, h1, h15, h7, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h0, h1, h19, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                          · linarith only [h13, h18, h19, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h17, h18, hc23, hlam, hphi, u3elo1]
                      · linarith only [h17, h4, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h0, h26, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                    · linarith only [h24, h26, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h2, h24, h25, h6, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
                  · linarith only [h0, h1, h24, h30, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h2, h30, h6, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h34 | h34
            · linarith only [h34, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
              · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                    · linarith only [h0, h39, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                    · linarith only [h37, h39, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h0, h2, h37, h38, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h1, h34, h37, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                    · linarith only [h0, h46, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                    · linarith only [h45, h46, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h2, h44, h45, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h1, h36, h4, h44, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h1, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h52 | h52
        · rcases m.htr 0 3 4 (by decide) (by decide) with h53 | h53
          · linarith only [h1, h2, h53, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h55 | h55
            · linarith only [h53, h55, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
              · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                  · linarith only [h2, h52, h59, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                    · linarith only [h0, h61, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                    · linarith only [h2, h52, h61, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h53, h58, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h2, h52, h57, hlam, hphi, u5ehi7, u5elo4]
        · linarith only [h1, h52, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h67 | h67
      · rcases m.htr 0 2 5 (by decide) (by decide) with h68 | h68
        · linarith only [h1, h68, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
        · linarith only [h67, h68, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h71 | h71
        · linarith only [h1, h71, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h73 | h73
          · rcases m.htr 0 3 5 (by decide) (by decide) with h74 | h74
            · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                · linarith only [h0, h1, h73, h75, h76, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                  · linarith only [h0, h67, h71, h75, h78, hlam, hphi, u5ehi9, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h0, h71, h80, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h86 | h86
                              · linarith only [h82, h86, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi9]
                              · rcases h2bigk with h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h71, hc12, hlam, hphi, ht23, ht34, ht45, p88_1, u5elo2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h1, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h67, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h71, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h76, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h78, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h80, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p88_1, u3elo2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p88_1, u3elo2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h67, h75, h86, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p88_1, u3elo2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p88_1, u3elo2, u5ehi7]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, h83, hc12, hlam, hphi, ht23, p88_1, u3elo2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h83, hc12, hlam, hphi, ht23, p88_1, u3elo2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h83, hlam, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, h71, h83, hc12, hlam, hphi, ht23, p88_1, u3elo2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p88_1, u5elo2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h1, h73, h75, h86, hc12, hc34, hlam, hphi, ht23, ht45, p88_1, u3elo2, u5elo2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h84, hlam, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h85, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                            · linarith only [h0, h1, h67, h73, h75, h85, hc12, hlam, hphi, ht23, u3elo2]
                          · linarith only [h1, h73, h75, h84, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi9]
                        · linarith only [h1, h73, h75, h83, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi9]
                      · linarith only [h73, h82, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                · linarith only [h0, h1, h118, h67, h74, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
                  · linarith only [h0, h120, h67, h75, hc24, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                    · linarith only [h0, h122, h67, h71, h75, hlam, hphi, u5ehi5, u5elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
                            · linarith only [h125, h127, h67, h75, hc02, hlam, hphi, ht23, u3elo2]
                            · linarith only [h0, h127, h67, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h1, h126, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h1, h124, h125, h74, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · linarith only [h124, h73, hc13, hlam, hphi, u3elo0]
            · linarith only [h73, h74, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h134 | h134
            · linarith only [h134, h73, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h136 | h136
              · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                · linarith only [h0, h1, h134, h137, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
                  · linarith only [h0, h1, h134, h136, h139, h67, hlam, hphi, u5ehi9, u5elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h141 | h141
                    · linarith only [h0, h1, h134, h141, h71, hlam, hphi, u5ehi5, u5elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                      · linarith only [h136, h143, h73, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi9]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                        · linarith only [h143, h145, hc13, hlam, hphi, u3elo2]
                        · linarith only [h0, h1, h145, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
                · linarith only [h0, h1, h148, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h150 | h150
                  · linarith only [h0, h150, h67, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
                    · linarith only [h0, h152, h71, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                      · linarith only [h0, h1, h154, h73, hc12, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                        · linarith only [h154, h156, hc13, hlam, hphi, u3elo2]
                        · linarith only [h0, h1, h156, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h159 | h159
    · rcases m.htr 0 2 4 (by decide) (by decide) with h160 | h160
      · rcases m.htr 0 2 5 (by decide) (by decide) with h161 | h161
        · rcases m.htr 0 3 4 (by decide) (by decide) with h162 | h162
          · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
            · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
              · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
                · rcases m.htr 1 2 4 (by decide) (by decide) with h166 | h166
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                          · linarith only [h159, h170, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                          · linarith only [h163, h170, hc23, hlam, hphi, u3elo0]
                        · linarith only [h168, h169, hc23, hlam, hphi, u3elo1]
                      · linarith only [h162, h168, hc13, hlam, hphi, u3elo0]
                    · linarith only [h0, h167, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h160, h166, hlam]
                · linarith only [h0, h159, h162, h164, h165, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi9]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                · rcases m.htr 1 2 4 (by decide) (by decide) with h179 | h179
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h180 | h180
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                          · linarith only [h159, h183, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                          · linarith only [h163, h183, hc23, hlam, hphi, u3elo0]
                        · linarith only [h181, h182, hc23, hlam, hphi, u3elo1]
                      · linarith only [h162, h164, h181, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h161, h180, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                  · linarith only [h0, h159, h160, h163, h164, h179, hlam, hphi, u5ehi8, u5elo4]
                · linarith only [h0, h159, h163, h178, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi8]
            · linarith only [h162, h163, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h192 | h192
            · linarith only [h162, h192, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
              · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                      · linarith only [h162, h198, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                        · linarith only [h159, h198, h200, hc13, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                          · linarith only [h192, h195, h202, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                            · linarith only [h160, h204, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
                            · linarith only [h162, h194, h200, h204, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h197, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h160, h196, hlam]
                · linarith only [h0, h159, h160, h194, h195, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi9]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
                · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h212 | h212
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h213 | h213
                      · linarith only [h162, h213, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h215 | h215
                        · linarith only [h159, h213, h215, hc13, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h217 | h217
                          · linarith only [h159, h162, h194, h217, hlam, hphi, u5ehi8, u5elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h219 | h219
                            · linarith only [h160, h194, h219, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h221 | h221
                              · linarith only [h162, h194, h221, hc03, hlam, hphi, u3elo3]
                              · linarith only [h159, h162, h221, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h161, h212, hlam]
                  · linarith only [h0, h160, h161, h211, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi7]
                · linarith only [h0, h159, h161, h210, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi7]
        · linarith only [h159, h161, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h228 | h228
        · rcases m.htr 0 3 4 (by decide) (by decide) with h229 | h229
          · linarith only [h159, h160, h229, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h231 | h231
            · linarith only [h229, h231, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h233 | h233
              · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                · rcases m.htr 1 2 4 (by decide) (by decide) with h235 | h235
                  · linarith only [h160, h228, h235, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h237 | h237
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h238 | h238
                      · linarith only [h229, h238, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                        · linarith only [h0, h159, h228, h235, h238, h240, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi7]
                        · linarith only [h160, h228, h240, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi7]
                    · linarith only [h0, h228, h237, hlam]
                · linarith only [h0, h159, h228, h231, h234, hlam, hphi, u5ehi7, u5elo3]
              · linarith only [h160, h228, h233, hlam, hphi, u5ehi7, u5elo4]
        · linarith only [h159, h228, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h247 | h247
      · rcases m.htr 0 2 5 (by decide) (by decide) with h248 | h248
        · linarith only [h159, h248, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
        · linarith only [h247, h248, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h251 | h251
        · linarith only [h159, h251, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h253 | h253
          · rcases m.htr 0 3 5 (by decide) (by decide) with h254 | h254
            · rcases m.htr 0 4 5 (by decide) (by decide) with h255 | h255
              · rcases m.htr 1 2 3 (by decide) (by decide) with h256 | h256
                · rcases m.htr 1 2 4 (by decide) (by decide) with h257 | h257
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h259 | h259
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h260 | h260
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h261 | h261
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h262 | h262
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h263 | h263
                              · linarith only [h159, h253, h256, h263, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi9]
                              · rcases h2bigk with h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h0, hlam, p265_1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h159, hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h247, hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h251, hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  rcases p265_3 (m.d 0 2) (by simp) with h271 | h271
                                  · linarith only [h0, h271, hlam]
                                  · rcases p265_3 (m.d 1 2) (by simp) with h273 | h273
                                    · rcases p265_3 (m.d 2 3) (by simp) with h274 | h274
                                      · linarith only [h256, h274, hlam]
                                      · linarith only [h159, h274, hlam]
                                    · linarith only [h0, h273, hlam]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h0, h159, hc01, hc12, hlam, hphi, p265_1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h0, h247, h251, h255, h258, h263, hc01, hc12, hc34, hlam, hphi, ht45, p265_1, u5elo1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h0, h251, hc01, hc12, hlam, hphi, p265_1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p265_1, u3elo2]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h256, hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h0, h247, h251, h255, h256, h258, h263, hc01, hc34, hlam, hphi, ht12, ht23, ht45, p265_1, u3elo1, u5elo1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h0, h251, h256, hc01, hlam, hphi, ht12, ht23, p265_1, u3elo1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h0, h257, hc01, hc12, hlam, hphi, p265_1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h257, hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h260, hlam, p265_1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h0, h251, h257, h259, hc01, hlam, hphi, ht12, ht23, p265_1, u3elo1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h0, h258, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p265_1, u5elo1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h258, hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h261, hlam, p265_1]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [h262, hlam, p265_0]
                                · have p265_0 := h265c.1
                                  have p265_1 := h265c.2.1
                                  have p265_2 := h265c.2.2.1
                                  have p265_3 := h265c.2.2.2
                                  linarith only [hlam, p265_0]
                            · linarith only [h0, h159, h247, h253, h255, h256, h262, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h159, h253, h255, h261, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi9]
                        · linarith only [h0, h159, h251, h253, h255, h258, h260, hc01, hlam, hphi, ht12, ht23, u3elo3, u5ehi9, u5elo1]
                      · linarith only [h253, h259, hc13, hlam, hphi, u3elo0]
                    · linarith only [h0, h159, h253, h255, h256, h258, hc01, hlam, hphi, ht12, ht23, u3elo1, u5ehi9, u5elo2]
                  · linarith only [h159, h253, h255, h256, h257, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                · linarith only [h0, h256, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h304 | h304
                · rcases m.htr 1 2 4 (by decide) (by decide) with h305 | h305
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h306 | h306
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h310 | h310
                            · linarith only [h0, h247, h255, h305, h307, h310, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h0, h247, h310, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h159, h254, h309, hlam]
                        · linarith only [h159, h253, h254, h255, h308, hlam, hphi, u5ehi8, u5elo4]
                      · linarith only [h159, h253, h254, h255, h304, h307, hlam, hphi, u5ehi8, u5elo4]
                    · linarith only [h159, h254, h304, h306, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                  · linarith only [h159, h254, h304, h305, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · linarith only [h0, h304, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h253, h254, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h320 | h320
            · linarith only [h253, h320, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h322 | h322
              · rcases m.htr 1 2 3 (by decide) (by decide) with h323 | h323
                · rcases m.htr 1 2 4 (by decide) (by decide) with h324 | h324
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h325 | h325
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h326 | h326
                      · linarith only [h0, h159, h253, h326, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h0, h159, h323, h326, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h159, h247, h320, h322, h324, h325, hc01, hc25, hlam, hphi, ht12, u5ehi9, u5elo3]
                  · linarith only [h0, h159, h323, h324, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h323, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                · rcases m.htr 1 2 4 (by decide) (by decide) with h333 | h333
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h335 | h335
                      · linarith only [h0, h159, h253, h335, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h0, h159, h332, h335, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h159, h332, h334, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h159, h332, h333, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h332, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_10_12_13_25_L_R_L_0_L_I_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0ehi := hb0.1
  have h0emin := hb0.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h10, h15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · linarith only [h14, h15, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                                · linarith only [h1, h11, h14, h18, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                                  · linarith only [h20, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                                    · linarith only [h1, h11, h14, h20, h22, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                                    · linarith only [h13, h14, h2, h22, h4, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                                · linarith only [h26, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · linarith only [h12, h13, h25, h26, h4, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · linarith only [h11, h13, h25, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · linarith only [h11, h12, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                          · linarith only [h11, h31, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                            · linarith only [h11, h33, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                              · linarith only [h10, h11, h33, h35, h4, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                                · linarith only [h10, h11, h31, h33, h37, h4, h7, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h39 | h39
                                  · linarith only [h11, h33, h39, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                                    · linarith only [h10, h11, h33, h4, h41, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                                    · linarith only [h10, h11, h4, h41, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h48 | h48
                            · linarith only [h48, h9, hc14, hlam, hphi, ht01, u0ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
                                · linarith only [h4, h51, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · linarith only [h1, h47, h50, h51, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                                · linarith only [h4, h54, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                                  · linarith only [h56, h9, hlam, hphi, ht01, ht12, u0ehi3, u2elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                                    · linarith only [h1, h4, h46, h58, h9, hlam, hphi, ht01, ht12, u0ehi3, u2elo0]
                                    · rcases h0emin with h60 | h60 | h60 | h60 | h60
                                      · rcases h3bigk with h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h4, h47, h50, h58, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p61_1, u2elo0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          rcases p61_3 (m.d 0 3) (by simp) with h64 | h64
                                          · rcases p61_3 (m.d 1 3) (by simp) with h65 | h65
                                            · linarith only [h1, h65, hlam]
                                            · linarith only [h45, h65, hlam]
                                          · linarith only [h4, h64, hlam]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h4, h50, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p61_1, u2elo0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h4, h50, h58, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p61_1, u2elo0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h1, hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          rcases p61_3 (m.d 0 3) (by simp) with h73 | h73
                                          · rcases p61_3 (m.d 1 3) (by simp) with h74 | h74
                                            · rcases p61_3 (m.d 2 3) (by simp) with h75 | h75
                                              · linarith only [h45, h75, hlam]
                                              · rcases p61_3 (m.d 3 4) (by simp) with h77 | h77
                                                · linarith only [h46, h77, hlam]
                                                · linarith only [h50, h77, hlam]
                                            · linarith only [h45, h74, hlam]
                                          · linarith only [h4, h73, hlam]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h1, h50, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p61_1]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h1, h4, h50, h58, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p61_1, u2elo0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h4, hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h45, hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h50, hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h54, hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h7, hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h46, hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h2, h46, h9, hc23, hc45, hlam, hphi, ht34, p61_1]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h58, hlam, p61_1]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h8, hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h47, hlam, p61_0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h1, h4, h47, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p61_1, u2elo0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [h1, h4, h47, h50, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p61_1, u2elo0]
                                        · have p61_0 := h61c.1
                                          have p61_1 := h61c.2.1
                                          have p61_2 := h61c.2.2.1
                                          have p61_3 := h61c.2.2.2
                                          linarith only [hlam, p61_0]
                                      · linarith only [h60, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h4, h60, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h60, h9, hc45, hlam, ht01, ht12, ht23, ht34]
                                      · linarith only [h6, h60, hlam, ht01, ht12, u2elo0]
                          · linarith only [h4, h46, h47, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
                          · linarith only [h104, h4, h46, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                            · linarith only [h106, h4, h46, h7, h9, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                              · linarith only [h108, h45, h46, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                                · linarith only [h104, h110, h45, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
                                  · linarith only [h112, h9, hlam, hphi, ht01, ht12, u0ehi3, u2elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h114 | h114
                                    · linarith only [h114, h4, h7, h9, hlam, hphi, ht01, ht12, u0ehi3, u2elo0]
                                    · rcases h0emin with h116 | h116 | h116 | h116 | h116
                                      · rcases h3bigk with h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          rcases p117_3 (m.d 0 3) (by simp) with h119 | h119
                                          · rcases p117_3 (m.d 1 3) (by simp) with h120 | h120
                                            · linarith only [h1, h120, hlam]
                                            · rcases p117_3 (m.d 2 3) (by simp) with h122 | h122
                                              · linarith only [h122, h4, hlam]
                                              · rcases p117_3 (m.d 3 4) (by simp) with h124 | h124
                                                · linarith only [h124, h7, hlam]
                                                · linarith only [h124, h46, hlam]
                                          · linarith only [h1, h119, hlam]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          rcases p117_3 (m.d 0 3) (by simp) with h128 | h128
                                          · rcases p117_3 (m.d 1 3) (by simp) with h129 | h129
                                            · linarith only [h1, h129, hlam]
                                            · linarith only [h129, h45, hlam]
                                          · linarith only [h128, h4, hlam]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h4, h45, h46, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p117_1, u2elo0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h104, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p117_1, u2elo0, u5ehi1]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h1, hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h46, hc23, hc34, hlam, hphi, p117_1]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h46, hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h104, hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h4, hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h45, hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h108, hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h110, hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h7, hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h4, h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p117_1, u2elo0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h4, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p117_1, u2elo0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h114, hlam, p117_1]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h8, hlam, p117_0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h4, h45, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p117_1, u2elo0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h4, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p117_1, u2elo0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p117_1, u2elo0]
                                        · have p117_0 := h117c.1
                                          have p117_1 := h117c.2.1
                                          have p117_2 := h117c.2.2.1
                                          have p117_3 := h117c.2.2.2
                                          linarith only [hlam, p117_0]
                                      · linarith only [h116, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h116, h4, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h116, h9, hc45, hlam, ht01, ht12, ht23, ht34]
                                      · linarith only [h116, h4, h8, hlam, ht01, ht12, u2elo0]
                      · linarith only [h4, h45, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h160 | h160
                    · linarith only [h160, h7, h8, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h162 | h162
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
                          · linarith only [h164, h8, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h166 | h166
                            · linarith only [h160, h166, hc14, hlam, hphi, ht01, u0ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h169 | h169
                                · linarith only [h0, h162, h169, h7, h8, hc02, hlam, hphi, u0ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h171 | h171
                                  · linarith only [h160, h171, hlam, hphi, ht01, ht12, u0ehi3, u2elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h173 | h173
                                    · linarith only [h0, h160, h162, h168, h173, hlam, hphi, ht01, ht12, u0ehi3, u2elo0]
                                    · rcases h0emin with h175 | h175 | h175 | h175 | h175
                                      · rcases h3bigk with h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h8, hc13, hc35, hlam, hphi, p176_1]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h173, h8, hc23, hc45, hlam, hphi, ht34, p176_1]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h173, h8, hc34, hc45, hlam, hphi, p176_1]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h8, hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h1, hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h1, h168, h173, h7, h8, hc01, hc34, hc45, hlam, hphi, p176_1, u0ehi3]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h1, h173, h8, hc34, hc45, hlam, hphi, p176_1]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h164, hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h4, hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h162, hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h173, h4, h7, h8, hc34, hc45, hlam, hphi, ht01, ht12, p176_1, u0ehi3, u2elo0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h169, hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h7, hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h163, hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h168, hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [hlam, p176_0]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h173, hlam, p176_1]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h173, h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p176_1, u0ehi3]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h163, h173, hc34, hc45, hlam, hphi, p176_1]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [h168, h173, hc34, hc45, hlam, hphi, p176_1]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          rcases p176_3 (m.d 0 3) (by simp) with h200 | h200
                                          · linarith only [h200, h8, hlam]
                                          · linarith only [h200, h7, hlam]
                                        · have p176_0 := h176c.1
                                          have p176_1 := h176c.2.1
                                          have p176_2 := h176c.2.2.1
                                          have p176_3 := h176c.2.2.2
                                          linarith only [hlam, p176_0]
                                      · linarith only [h175, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h175, h4, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h175, h5, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h175, h6, hlam, ht01, ht12, u2elo0]
                              · linarith only [h168, h7, h8, hc23, hc35, hlam, hphi]
                        · linarith only [h162, h163, h7, h8, hc23, hc35, hlam, hphi]
                      · linarith only [h162, h4, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h211 | h211
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h212 | h212
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                        · linarith only [h211, h214, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h216 | h216
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h217 | h217
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h218 | h218
                              · linarith only [h211, h218, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h220 | h220
                                · linarith only [h220, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · linarith only [h1, h216, h220, h7, hc23, hc34, hlam, hphi]
                            · linarith only [h212, h214, h216, h217, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                          · linarith only [h211, h216, h7, hc13, hc34, hlam, hphi]
                      · linarith only [h213, h4, hc12, hlam, hphi, u2elo0]
                    · linarith only [h211, h212, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h227 | h227
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h228 | h228
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                        · linarith only [h229, h7, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h231 | h231
                          · linarith only [h1, h211, h231, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h233 | h233
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                              · linarith only [h0, h228, h234, h7, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                                · linarith only [h0, h211, h228, h236, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h238 | h238
                                  · linarith only [h238, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h240 | h240
                                    · rcases h0emin with h241 | h241 | h241 | h241 | h241
                                      · rcases h3bigk with h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h211, h240, hc13, hc34, hlam, hphi, p242_1]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h211, h240, hc23, hc34, hlam, hphi, p242_1]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h7, hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h211, hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h1, hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h1, h211, h240, hc23, hc34, hlam, hphi, p242_1]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h229, hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h231, hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h4, hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h228, hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h234, hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h236, hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p242_1, u0ehi2]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          rcases p242_3 (m.d 0 3) (by simp) with h259 | h259
                                          · linarith only [h259, h7, hlam]
                                          · linarith only [h1, h259, hlam]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          rcases p242_3 (m.d 0 3) (by simp) with h262 | h262
                                          · linarith only [h262, h7, hlam]
                                          · linarith only [h262, h4, hlam]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h2, h211, h233, h234, h238, h5, hc23, hc34, hlam, hphi, ht01, ht12, p242_1, u0ehi2, u2elo0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h2, h233, h234, h238, h5, hc23, hc35, hlam, hphi, ht01, ht12, p242_1, u0ehi2, u2elo0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          rcases p242_3 (m.d 0 3) (by simp) with h268 | h268
                                          · linarith only [h211, h268, hlam]
                                          · linarith only [h1, h268, hlam]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          rcases p242_3 (m.d 0 3) (by simp) with h271 | h271
                                          · linarith only [h211, h271, hlam]
                                          · linarith only [h271, h4, hlam]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [h240, hlam, p242_0]
                                        · have p242_0 := h242c.1
                                          have p242_1 := h242c.2.1
                                          have p242_2 := h242c.2.2.1
                                          have p242_3 := h242c.2.2.2
                                          linarith only [hlam, p242_0]
                                      · linarith only [h241, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h241, h4, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h241, h5, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h241, h6, hlam, ht01, ht12, u2elo0]
                                    · linarith only [h2, h233, h240, h5, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                              · linarith only [h227, h228, h229, h233, h281, h5, h7, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h283 | h283
                                · linarith only [h227, h228, h229, h233, h283, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h285 | h285
                                  · linarith only [h228, h229, h233, h285, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h287 | h287
                                    · rcases h0emin with h288 | h288 | h288 | h288 | h288
                                      · rcases h3bigk with h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h211, h228, h287, hc23, hc34, hlam, hphi, p289_1]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h211, h287, hc23, hc34, hlam, hphi, p289_1]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h7, hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h211, hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h1, hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h229, h233, hc23, hc45, hlam, hphi, ht34, p289_1]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h229, hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h231, hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h4, hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h228, hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h281, hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h283, hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p289_1, u0ehi2]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          rcases p289_3 (m.d 0 3) (by simp) with h306 | h306
                                          · linarith only [h306, h7, hlam]
                                          · linarith only [h1, h306, hlam]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          rcases p289_3 (m.d 0 3) (by simp) with h309 | h309
                                          · linarith only [h309, h7, hlam]
                                          · linarith only [h309, h4, hlam]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h211, h227, h228, h229, h233, h5, hc23, hc34, hlam, hphi, ht01, ht12, p289_1, u0ehi2, u2elo0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h227, h228, h229, h233, h5, hc23, hc35, hlam, hphi, ht01, ht12, p289_1, u0ehi2, u2elo0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          rcases p289_3 (m.d 0 3) (by simp) with h315 | h315
                                          · linarith only [h211, h315, hlam]
                                          · linarith only [h1, h315, hlam]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          rcases p289_3 (m.d 0 3) (by simp) with h318 | h318
                                          · linarith only [h211, h318, hlam]
                                          · linarith only [h318, h4, hlam]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [h287, hlam, p289_0]
                                        · have p289_0 := h289c.1
                                          have p289_1 := h289c.2.1
                                          have p289_2 := h289c.2.2.1
                                          have p289_3 := h289c.2.2.2
                                          linarith only [hlam, p289_0]
                                      · linarith only [h288, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h288, h4, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h288, h5, hlam, ht01, ht12, u2elo0]
                                      · linarith only [h227, h288, h5, hlam, ht01, ht12, u2elo0]
                                    · linarith only [h227, h287, h5, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h228, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
                        · linarith only [h330, h7, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
                          · linarith only [h1, h211, h332, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h334 | h334
                            · linarith only [h227, h334, hc14, hlam, hphi, ht01, u0ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                              · linarith only [h336, h7, hlam, hphi, ht01, ht12, u0ehi2, u2elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
                                · linarith only [h0, h211, h329, h338, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h340 | h340
                                  · linarith only [h227, h340, h7, hlam, hphi, ht01, ht12, u0ehi2, u2elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h342 | h342
                                    · linarith only [h227, h342, h7, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h342, h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                      · linarith only [h329, h4, hc12, hlam, hphi, u2elo0]
              · linarith only [h6, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
            · linarith only [h4, h5, hlam, hphi, ht01, ht12, u0ehi2, u2elo3]
          · linarith only [h4, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h349 | h349
          · rcases m.htr 0 2 4 (by decide) (by decide) with h350 | h350
            · rcases m.htr 0 2 5 (by decide) (by decide) with h351 | h351
              · linarith only [h0, h3, h351, hlam]
              · linarith only [h351, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
            · linarith only [h349, h350, hlam, hphi, ht01, ht12, u0ehi2, u2elo3]
          · linarith only [h349, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h356 | h356
        · rcases m.htr 0 2 3 (by decide) (by decide) with h357 | h357
          · rcases m.htr 0 2 4 (by decide) (by decide) with h358 | h358
            · linarith only [h0, h2, h358, hlam]
            · linarith only [h357, h358, hlam, hphi, ht01, ht12, u0ehi2, u2elo3]
          · linarith only [h357, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h362 | h362
          · rcases m.htr 0 2 4 (by decide) (by decide) with h363 | h363
            · linarith only [h0, h2, h363, hlam]
            · linarith only [h362, h363, hlam, hphi, ht01, ht12, u0ehi2, u2elo3]
          · linarith only [h362, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h367 | h367
      · rcases m.htr 0 1 5 (by decide) (by decide) with h368 | h368
        · rcases m.htr 0 2 3 (by decide) (by decide) with h369 | h369
          · linarith only [h0, h1, h369, hlam]
          · linarith only [h369, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h372 | h372
          · linarith only [h0, h1, h372, hlam]
          · linarith only [h372, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h375 | h375
        · rcases m.htr 0 2 3 (by decide) (by decide) with h376 | h376
          · linarith only [h0, h1, h376, hlam]
          · linarith only [h376, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h379 | h379
          · linarith only [h0, h1, h379, hlam]
          · linarith only [h379, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

end R2N4
