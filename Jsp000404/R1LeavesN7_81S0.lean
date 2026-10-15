import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_I_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h11, h13, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h12, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                          · linarith only [h11, h17, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · linarith only [h17, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h10, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h5, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h4, h8, hc12, hlam, hphi, u2elo0]
                · linarith only [h7, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                        · linarith only [h1, h24, h28, h6, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                            · linarith only [h1, h25, h30, h31, h6, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                              · linarith only [h0, h26, h31, h33, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h1, h30, h33, h6, hc23, hc34, hlam, hphi]
                          · linarith only [h24, h30, hc13, hlam, hphi, ht34, ht45, u5elo0]
                      · linarith only [h27, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h25, h26, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h25, h4, hc12, hlam, hphi, u2elo0]
                · linarith only [h24, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h41 | h41
              · linarith only [h4, h41, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h43 | h43
                · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                    · linarith only [h0, h45, h5, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                        · linarith only [h1, h41, h48, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                            · linarith only [h0, h1, h41, h44, h50, h51, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                              · linarith only [h0, h44, h5, h53, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                              · linarith only [h53, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h4, h43, h5, h50, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h47, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h4, h44, h5, hc12, hlam, hphi, u2elo3]
                · linarith only [h43, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h60 | h60
            · rcases m.htr 0 3 4 (by decide) (by decide) with h61 | h61
              · rcases m.htr 0 3 5 (by decide) (by decide) with h62 | h62
                · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
                  · linarith only [h4, h63, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h66 | h66
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                                · linarith only [h0, h4, h65, h71, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                                · linarith only [h71, hc24, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h4, h65, h69, h70, hc34, hlam, hphi, ht45, u5elo3]
                            · linarith only [h4, h61, h69, hlam]
                          · linarith only [h68, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h4, h61, h63, h67, hc12, hlam, hphi, u2elo2]
                      · linarith only [h65, h66, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h4, h60, h65, hc12, hlam, hphi, u2elo2]
                · linarith only [h62, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h4, h60, h61, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h82 | h82
              · rcases m.htr 0 3 5 (by decide) (by decide) with h83 | h83
                · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                  · linarith only [h4, h84, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                    · linarith only [h0, h60, h86, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h93 | h93
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                                  · linarith only [h1, h89, h94, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h94, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h0, h60, h88, h92, h93, hc35, hlam, hphi, u5elo4]
                              · linarith only [h60, h91, h92, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                            · linarith only [h0, h4, h82, h88, h91, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h90, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h4, h82, h84, h88, h89, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · linarith only [h88, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h83, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h104 | h104
                · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                  · linarith only [h0, h105, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                    · linarith only [h0, h107, h60, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                        · linarith only [h1, h110, h4, h82, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                            · linarith only [h0, h109, h113, h4, h82, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h117 | h117
                                  · rcases h3bigk with h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h105, h109, h115, h117, hc45, hlam, hphi, ht0b, ht5b, p118_1, u0elo2]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h4, hlam, p118_1]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h82, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      rcases p118_3 (m.d 0 3) (by simp) with h123 | h123
                                      · rcases p118_3 (m.d 1 3) (by simp) with h124 | h124
                                        · linarith only [h1, h124, hlam]
                                        · linarith only [h112, h124, hlam]
                                      · linarith only [h123, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h1, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h105, hlam, p118_1]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h110, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h1, h117, hc45, hlam, hphi, ht0b, ht5b, p118_1, u0elo0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h113, hc03, hc34, hlam, hphi, p118_1]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h113, hc13, hc34, hlam, hphi, p118_1]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h113, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      rcases p118_3 (m.d 0 3) (by simp) with h137 | h137
                                      · linarith only [h137, h4, hlam]
                                      · linarith only [h104, h137, hlam]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      rcases p118_3 (m.d 0 3) (by simp) with h140 | h140
                                      · linarith only [h140, hlam, p118_0]
                                      · rcases p118_3 (m.d 1 3) (by simp) with h142 | h142
                                        · linarith only [h110, h142, hlam]
                                        · rcases p118_3 (m.d 2 3) (by simp) with h144 | h144
                                          · linarith only [h113, h144, hlam]
                                          · linarith only [h144, h4, hlam]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      rcases p118_3 (m.d 0 3) (by simp) with h147 | h147
                                      · linarith only [h147, h82, hlam]
                                      · linarith only [h1, h147, hlam]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h0, h109, h115, h117, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p118_1]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h0, h109, h113, h115, h4, hlam, p118_2]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h104, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h112, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h115, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h117, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [hlam, p118_0]
                                  · linarith only [h0, h109, h113, h115, h117, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h0, h109, h113, h115, h116, h4, hc35, hlam, hphi, u5elo4]
                              · linarith only [h115, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h104, h105, h109, h112, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h109, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h104, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h165 | h165
        · rcases m.htr 0 2 3 (by decide) (by decide) with h166 | h166
          · rcases m.htr 0 2 4 (by decide) (by decide) with h167 | h167
            · linarith only [h0, h167, h2, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h169 | h169
              · linarith only [h1, h169, h2, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h171 | h171
                · rcases m.htr 1 2 3 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
                    · linarith only [h0, h167, h173, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h172, h173, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h166, h172, hc12, hlam, hphi, u2elo0]
                · linarith only [h171, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h178 | h178
            · linarith only [h1, h166, h178, h2, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h180 | h180
              · linarith only [h1, h180, h2, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h182 | h182
                · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                  · linarith only [h0, h166, h183, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h185 | h185
                    · linarith only [h0, h178, h185, h2, hlam]
                    · linarith only [h1, h183, h185, h2, hc12, hlam, hphi, u2elo3]
                · linarith only [h166, h182, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h165, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h190 | h190
      · rcases m.htr 0 1 5 (by decide) (by decide) with h191 | h191
        · rcases m.htr 0 2 3 (by decide) (by decide) with h192 | h192
          · linarith only [h0, h1, h192, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h194 | h194
            · rcases m.htr 0 3 4 (by decide) (by decide) with h195 | h195
              · rcases m.htr 0 3 5 (by decide) (by decide) with h196 | h196
                · rcases m.htr 1 2 3 (by decide) (by decide) with h197 | h197
                  · linarith only [h0, h192, h197, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h197, hc12, hlam, hphi, u2elo2]
                · linarith only [h196, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h1, h194, h195, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h202 | h202
              · rcases m.htr 0 3 5 (by decide) (by decide) with h203 | h203
                · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
                  · linarith only [h0, h192, h204, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h204, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h203, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h1, h190, h202, hlam]
        · linarith only [h0, h191, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h210 | h210
        · rcases m.htr 0 2 3 (by decide) (by decide) with h211 | h211
          · linarith only [h0, h1, h211, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h213 | h213
            · linarith only [h0, h190, h213, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h215 | h215
              · rcases m.htr 0 3 5 (by decide) (by decide) with h216 | h216
                · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                  · linarith only [h0, h211, h217, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h217, hc12, hlam, hphi, u2elo2]
                · linarith only [h216, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h221 | h221
                · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                  · linarith only [h0, h1, h215, h222, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h222, hc12, hlam, hphi, u2elo2]
                · linarith only [h221, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h0, h210, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h227 | h227
    · rcases m.htr 0 1 4 (by decide) (by decide) with h228 | h228
      · rcases m.htr 0 1 5 (by decide) (by decide) with h229 | h229
        · rcases m.htr 0 2 3 (by decide) (by decide) with h230 | h230
          · rcases m.htr 0 2 4 (by decide) (by decide) with h231 | h231
            · rcases m.htr 0 3 4 (by decide) (by decide) with h232 | h232
              · rcases m.htr 0 3 5 (by decide) (by decide) with h233 | h233
                · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h235 | h235
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h236 | h236
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h237 | h237
                        · linarith only [h0, h227, h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h227, h232, h234, h237, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h236, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h227, h234, h235, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h227, h234, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h232, h233, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h244 | h244
                · rcases m.htr 1 2 3 (by decide) (by decide) with h245 | h245
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h246 | h246
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h247 | h247
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h248 | h248
                        · linarith only [h227, h232, h248, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h250 | h250
                          · linarith only [h0, h228, h248, h250, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h232, h244, h245, h250, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h247, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h227, h245, h246, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h227, h245, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h244, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h0, h228, h231, hlam]
          · linarith only [h0, h227, h230, hlam]
        · linarith only [h227, h229, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h260 | h260
        · rcases m.htr 0 2 3 (by decide) (by decide) with h261 | h261
          · rcases m.htr 0 2 4 (by decide) (by decide) with h262 | h262
            · rcases m.htr 0 3 4 (by decide) (by decide) with h263 | h263
              · linarith only [h227, h228, h263, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h265 | h265
                · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h268 | h268
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h269 | h269
                        · linarith only [h227, h263, h269, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                          · linarith only [h227, h228, h267, h271, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h266, h271, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h228, h267, h268, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h262, h267, hlam]
                  · linarith only [h0, h227, h266, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h265, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h278 | h278
              · linarith only [h227, h228, h278, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h280 | h280
                · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h282 | h282
                    · linarith only [h0, h262, h282, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h227, h281, h282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h281, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h280, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h0, h227, h261, hlam]
        · linarith only [h227, h260, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h289 | h289
      · rcases m.htr 0 1 5 (by decide) (by decide) with h290 | h290
        · rcases m.htr 0 2 3 (by decide) (by decide) with h291 | h291
          · rcases m.htr 0 2 4 (by decide) (by decide) with h292 | h292
            · rcases m.htr 0 3 4 (by decide) (by decide) with h293 | h293
              · rcases m.htr 0 3 5 (by decide) (by decide) with h294 | h294
                · rcases m.htr 1 2 3 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h296 | h296
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h297 | h297
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h298 | h298
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h299 | h299
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h300 | h300
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h301 | h301
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h302 | h302
                                · linarith only [h227, h289, h295, h296, h302, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · linarith only [h302, hc24, hlam, hphi, ht45, u5elo4]
                              · linarith only [h301, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h227, h289, h295, h298, h300, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h227, h299, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h227, h289, h293, h296, h298, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h227, h289, h295, h296, h297, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h227, h295, h296, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h289, h295, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h294, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h227, h289, h293, hlam]
            · linarith only [h227, h289, h291, h292, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h315 | h315
            · rcases m.htr 0 3 4 (by decide) (by decide) with h316 | h316
              · rcases m.htr 0 3 5 (by decide) (by decide) with h317 | h317
                · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
                  · linarith only [h291, h318, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h289, h318, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h0, h289, h291, h317, hc14, hlam, hphi, ht45, u5elo3]
              · linarith only [h0, h289, h291, h316, hlam]
            · linarith only [h0, h289, h315, hlam]
        · linarith only [h289, h290, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h325 | h325
        · rcases m.htr 0 2 3 (by decide) (by decide) with h326 | h326
          · rcases m.htr 0 2 4 (by decide) (by decide) with h327 | h327
            · rcases m.htr 0 3 4 (by decide) (by decide) with h328 | h328
              · rcases m.htr 0 3 5 (by decide) (by decide) with h329 | h329
                · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h332 | h332
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h333 | h333
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h334 | h334
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h338 | h338
                                  · linarith only [h326, h335, h338, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h338, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h337, hc24, hlam, hphi, ht45, u5elo4]
                              · linarith only [h336, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
                              · linarith only [h328, h335, h343, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h343, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h289, h325, h329, h332, h333, h334, hc25, hlam, hphi, u5elo0]
                        · linarith only [h227, h328, h333, hlam]
                      · linarith only [h227, h328, h330, h332, hc34, hlam, hphi, ht45, u5elo2]
                    · linarith only [h227, h325, h330, h331, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h325, h330, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h289, h325, h328, h329, hc15, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h352 | h352
                · rcases m.htr 1 2 3 (by decide) (by decide) with h353 | h353
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h354 | h354
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h355 | h355
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h356 | h356
                        · linarith only [h328, h352, h353, h356, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h358 | h358
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h359 | h359
                            · linarith only [h227, h325, h326, h355, h356, h359, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h361 | h361
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h362 | h362
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h363 | h363
                                  · rcases h3bigk with h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h227, hlam, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h328, hc23, hc34, hlam, hphi, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h328, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 3) (by simp) with h369 | h369
                                      · rcases p364_3 (m.d 1 3) (by simp) with h370 | h370
                                        · rcases p364_3 (m.d 2 3) (by simp) with h371 | h371
                                          · linarith only [h326, h371, hlam]
                                          · linarith only [h361, h371, hlam]
                                        · linarith only [h358, h370, hlam]
                                      · linarith only [h369, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h356, hc03, hc34, hlam, hphi, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h356, h361, h363, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h356, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 3) (by simp) with h380 | h380
                                      · linarith only [h227, h380, hlam]
                                      · linarith only [h352, h380, hlam]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h326, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h353, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h359, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h0, h326, h363, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p364_1, u2elo1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 3) (by simp) with h388 | h388
                                      · linarith only [h388, hlam, p364_0]
                                      · rcases p364_3 (m.d 1 3) (by simp) with h390 | h390
                                        · linarith only [h356, h390, hlam]
                                        · linarith only [h227, h390, hlam]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h227, h325, h355, h361, h363, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 3) (by simp) with h394 | h394
                                      · linarith only [h328, h394, hlam]
                                      · linarith only [h326, h394, hlam]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h227, h325, h355, h356, h361, hlam, p364_2]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h352, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h358, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h361, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h363, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                  · linarith only [h227, h325, h355, h356, h361, h363, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h362, hc24, hlam, hphi, ht45, u5elo4]
                              · linarith only [h361, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h227, h352, h358, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h355, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h325, h354, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h325, h353, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h352, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h412 | h412
              · linarith only [h326, h327, h412, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h414 | h414
                · rcases m.htr 1 2 3 (by decide) (by decide) with h415 | h415
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h416 | h416
                    · linarith only [h327, h416, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h325, h416, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h325, h326, h415, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h414, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h421 | h421
            · rcases m.htr 0 3 4 (by decide) (by decide) with h422 | h422
              · rcases m.htr 0 3 5 (by decide) (by decide) with h423 | h423
                · rcases m.htr 1 2 3 (by decide) (by decide) with h424 | h424
                  · linarith only [h326, h424, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h325, h424, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h289, h325, h326, h421, h423, hc15, hlam, hphi, u5elo3]
              · linarith only [h326, h421, h422, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h429 | h429
              · rcases m.htr 0 3 5 (by decide) (by decide) with h430 | h430
                · rcases m.htr 1 2 3 (by decide) (by decide) with h431 | h431
                  · linarith only [h0, h325, h326, h431, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h325, h431, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h0, h325, h421, h429, h430, hc15, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h435 | h435
                · rcases m.htr 1 2 3 (by decide) (by decide) with h436 | h436
                  · linarith only [h0, h325, h326, h436, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h325, h436, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h435, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h325, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem r1l7_10_12_13_25_L_0_L_I_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h0, h4, h5, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h3, h5, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, h2, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
                · linarith only [h0, h13, h2, h5, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h1, h16, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h16, h19, h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h11, h18, h19, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h15, h18, hc23, hlam, hphi, u3elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h15, h23, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                      · linarith only [h15, h2, h25, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h25, h5, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h30, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                    · linarith only [h1, h33, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                      · linarith only [h0, h28, h35, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h32, h33, h35, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h38 | h38
                    · linarith only [h32, h38, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                      · linarith only [h32, h40, hc13, hlam, hphi, u3elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
                        · linarith only [h28, h30, h32, h38, h42, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h0, h29, h4, h40, h42, hc23, hlam, hphi, u3elo4]
              · linarith only [h29, h3, h4, hc12, hc25, hlam, hphi]
            · linarith only [h2, h28, h4, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h47 | h47
          · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
            · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
              · linarith only [h0, h3, h49, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                · linarith only [h0, h51, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h47, h48, h51, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2, h3, h48, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
            · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
              · linarith only [h0, h3, h56, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
                · linarith only [h0, h47, h58, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
                  · linarith only [h55, h56, h60, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                    · linarith only [h60, h62, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                      · linarith only [h60, h64, hc13, hlam, hphi, u3elo2]
                      · linarith only [h0, h3, h55, h64, hc23, hlam, hphi, u3elo3]
            · linarith only [h2, h3, h55, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h68 | h68
        · rcases m.htr 0 2 5 (by decide) (by decide) with h69 | h69
          · linarith only [h2, h69, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
            · linarith only [h0, h2, h71, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
              · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                · linarith only [h0, h2, h69, h74, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                    · linarith only [h1, h77, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                        · linarith only [h77, h80, hc13, hlam, hphi, u3elo2]
                        · linarith only [h0, h2, h73, h79, h80, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h2, h73, h79, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h71, h73, h76, hlam]
              · linarith only [h2, h68, h73, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h86 | h86
          · linarith only [h2, h86, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
            · linarith only [h0, h2, h88, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
              · linarith only [h68, h88, h90, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h92 | h92
                · linarith only [h0, h86, h92, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                    · linarith only [h1, h95, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                        · linarith only [h95, h98, hc13, hlam, hphi, u3elo2]
                        · linarith only [h0, h2, h98, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h0, h2, h97, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                    · linarith only [h102, h94, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                      · linarith only [h104, h94, hc13, hlam, hphi, u3elo2]
                      · linarith only [h0, h104, h2, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h108 | h108
    · rcases m.htr 0 2 3 (by decide) (by decide) with h109 | h109
      · rcases m.htr 0 2 4 (by decide) (by decide) with h110 | h110
        · rcases m.htr 0 2 5 (by decide) (by decide) with h111 | h111
          · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
            · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
              · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
                · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                    · linarith only [h108, h116, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                        · linarith only [h112, h116, h119, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                          · linarith only [h110, h121, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                            · linarith only [h115, h116, h121, h123, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · rcases h2bigk with h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h0, hlam, p125_1]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h118, hc34, hlam, hphi, ht0b, ht45, ht5b, p125_1, u0elo1]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                rcases p125_3 (m.d 0 2) (by simp) with h129 | h129
                                · rcases p125_3 (m.d 1 2) (by simp) with h130 | h130
                                  · rcases p125_3 (m.d 2 3) (by simp) with h131 | h131
                                    · linarith only [h109, h131, hlam]
                                    · linarith only [h118, h131, hlam]
                                  · linarith only [h113, h130, hlam]
                                · linarith only [h129, hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h118, h119, hc34, hlam, hphi, ht0b, ht45, ht5b, p125_1, u0elo1]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h109, h118, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p125_1]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                rcases p125_3 (m.d 0 2) (by simp) with h139 | h139
                                · linarith only [h0, h139, hlam]
                                · linarith only [h109, h139, hlam]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                rcases p125_3 (m.d 0 2) (by simp) with h142 | h142
                                · linarith only [h0, h142, hlam]
                                · linarith only [h110, h142, hlam]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                rcases p125_3 (m.d 0 2) (by simp) with h145 | h145
                                · linarith only [h0, h145, hlam]
                                · linarith only [h111, h145, hlam]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h109, hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h112, hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h108, h112, hc24, hlam, hphi, ht0b, ht45, ht5b, p125_1, u0elo0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h119, hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h110, hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h113, hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h118, hlam, p125_1]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h121, hlam, p125_1]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h111, hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h114, hlam, p125_0]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h111, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p125_1, u0elo1]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [h111, h118, hc34, hlam, hphi, ht0b, ht45, ht5b, p125_1, u0elo1]
                              · have p125_0 := h125c.1
                                have p125_1 := h125c.2.1
                                have p125_2 := h125c.2.2.1
                                have p125_3 := h125c.2.2.2
                                linarith only [hlam, p125_0]
                      · linarith only [h115, h116, h118, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
                    · linarith only [h115, h164, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                      · linarith only [h115, h166, hc13, hlam, hphi, u3elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
                        · linarith only [h112, h164, h168, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h170 | h170
                          · linarith only [h110, h170, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h172 | h172
                            · linarith only [h166, h170, h172, hc23, hlam, hphi, u3elo3]
                            · rcases h2bigk with h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h0, hlam, p174_1]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                rcases p174_3 (m.d 0 2) (by simp) with h177 | h177
                                · rcases p174_3 (m.d 1 2) (by simp) with h178 | h178
                                  · rcases p174_3 (m.d 2 3) (by simp) with h179 | h179
                                    · linarith only [h179, hlam, p174_0]
                                    · rcases p174_3 (m.d 2 4) (by simp) with h181 | h181
                                      · linarith only [h110, h181, hlam]
                                      · linarith only [h166, h181, hlam]
                                  · linarith only [h112, h178, hlam]
                                · linarith only [h177, hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                rcases p174_3 (m.d 0 2) (by simp) with h186 | h186
                                · rcases p174_3 (m.d 1 2) (by simp) with h187 | h187
                                  · rcases p174_3 (m.d 2 3) (by simp) with h188 | h188
                                    · linarith only [h109, h188, hlam]
                                    · rcases p174_3 (m.d 2 4) (by simp) with h190 | h190
                                      · linarith only [h190, hlam, p174_0]
                                      · rcases p174_3 (m.d 2 5) (by simp) with h192 | h192
                                        · linarith only [h111, h192, hlam]
                                        · linarith only [h170, h192, hlam]
                                  · linarith only [h113, h187, hlam]
                                · linarith only [h186, hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p174_1, u0elo1, u5ehi2]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h111, hc12, hlam, hphi, ht01, ht0b, ht5b, p174_1, u5ehi2]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                rcases p174_3 (m.d 0 2) (by simp) with h200 | h200
                                · linarith only [h0, h200, hlam]
                                · linarith only [h109, h200, hlam]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                rcases p174_3 (m.d 0 2) (by simp) with h203 | h203
                                · linarith only [h0, h203, hlam]
                                · linarith only [h110, h203, hlam]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                rcases p174_3 (m.d 0 2) (by simp) with h206 | h206
                                · linarith only [h0, h206, hlam]
                                · linarith only [h111, h206, hlam]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h109, hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h112, hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h166, hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h168, hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h110, hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h113, hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h110, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p174_1, u0elo1]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h170, hlam, p174_1]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h111, hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h114, hlam, p174_0]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h111, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p174_1, u0elo1]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [h111, hc24, hlam, hphi, ht0b, ht45, ht5b, p174_1, u0elo1]
                              · have p174_0 := h174c.1
                                have p174_1 := h174c.2.1
                                have p174_2 := h174c.2.2.1
                                have p174_3 := h174c.2.2.2
                                linarith only [hlam, p174_0]
                · linarith only [h0, h111, h114, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h110, h113, hlam]
            · linarith only [h0, h112, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h227 | h227
            · rcases m.htr 1 2 4 (by decide) (by decide) with h228 | h228
              · rcases m.htr 1 2 5 (by decide) (by decide) with h229 | h229
                · rcases m.htr 1 3 4 (by decide) (by decide) with h230 | h230
                  · linarith only [h0, h108, h111, h229, h230, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h232 | h232
                    · linarith only [h0, h108, h111, h229, h232, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h0, h108, h111, h227, h229, h232, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
                  · linarith only [h0, h108, h229, h235, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
                    · linarith only [h0, h108, h229, h237, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h108, h229, h237, hc13, hlam, hphi, u3elo4]
              · linarith only [h0, h108, h110, h227, h228, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h108, h227, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h242 | h242
          · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
            · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
              · linarith only [h110, h242, h244, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h246 | h246
                · rcases m.htr 1 3 4 (by decide) (by decide) with h247 | h247
                  · linarith only [h0, h108, h244, h247, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h108, h243, h244, h247, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h108, h242, h243, h246, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h243, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h252 | h252
            · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
              · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
                · rcases m.htr 1 3 4 (by decide) (by decide) with h255 | h255
                  · linarith only [h0, h108, h110, h253, h255, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h108, h110, h252, h253, h255, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h108, h110, h252, h253, h254, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h259 | h259
                · linarith only [h0, h108, h242, h252, h253, h259, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
                  · linarith only [h0, h108, h253, h261, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h108, h253, h261, hc13, hlam, hphi, u3elo3]
            · linarith only [h0, h108, h252, hc13, hlam, hphi, u3elo2]
      · linarith only [h0, h108, h109, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h266 | h266
      · rcases m.htr 0 2 4 (by decide) (by decide) with h267 | h267
        · rcases m.htr 0 2 5 (by decide) (by decide) with h268 | h268
          · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
            · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
              · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h273 | h273
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                        · linarith only [h266, h275, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · linarith only [h273, h275, hc23, hlam, hphi, u3elo1]
                      · linarith only [h272, h274, hc23, hlam, hphi, u3elo1]
                    · linarith only [h108, h273, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h108, h272, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h268, h271, hlam]
              · linarith only [h0, h267, h270, hlam]
            · linarith only [h0, h268, h269, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h284 | h284
            · rcases m.htr 1 2 4 (by decide) (by decide) with h285 | h285
              · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
                · rcases m.htr 1 3 4 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h288 | h288
                    · linarith only [h266, h268, h286, h288, hc23, hlam, hphi, u3elo1]
                    · linarith only [h108, h288, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h108, h287, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h292 | h292
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h293 | h293
                    · linarith only [h284, h286, h293, hlam]
                    · linarith only [h108, h293, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h108, h292, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h267, h285, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h284, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h299 | h299
          · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
            · rcases m.htr 1 2 4 (by decide) (by decide) with h301 | h301
              · linarith only [h267, h299, h301, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h303 | h303
                · rcases m.htr 1 3 4 (by decide) (by decide) with h304 | h304
                  · linarith only [h300, h301, h304, hlam]
                  · linarith only [h108, h304, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h299, h303, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h300, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h309 | h309
            · rcases m.htr 1 2 4 (by decide) (by decide) with h310 | h310
              · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
                · rcases m.htr 1 3 4 (by decide) (by decide) with h312 | h312
                  · linarith only [h266, h267, h310, h312, hc23, hlam, hphi, u3elo1]
                  · linarith only [h108, h312, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h266, h267, h310, h311, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h316 | h316
                · linarith only [h266, h299, h310, h316, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h318 | h318
                  · linarith only [h309, h310, h318, hlam]
                  · linarith only [h108, h318, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h0, h266, h309, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h322 | h322
        · rcases m.htr 0 2 5 (by decide) (by decide) with h323 | h323
          · linarith only [h266, h323, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h325 | h325
            · rcases m.htr 1 2 4 (by decide) (by decide) with h326 | h326
              · rcases m.htr 1 2 5 (by decide) (by decide) with h327 | h327
                · rcases m.htr 1 3 4 (by decide) (by decide) with h328 | h328
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h329 | h329
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h330 | h330
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h332 | h332
                          · linarith only [h322, h323, h327, h329, h332, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h334 | h334
                            · linarith only [h323, h332, h334, hc02, hlam, hphi, ht23, u3elo3]
                            · rcases h2bigk with h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [hlam, p336_0]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h0, hlam, p336_1]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h266, hlam, p336_0]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h323, h330, h332, hc34, hc45, hlam, hphi, p336_1]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h323, hlam, p336_0]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                rcases p336_3 (m.d 0 2) (by simp) with h342 | h342
                                · linarith only [h0, h342, hlam]
                                · rcases p336_3 (m.d 1 2) (by simp) with h344 | h344
                                  · rcases p336_3 (m.d 2 3) (by simp) with h345 | h345
                                    · linarith only [h325, h345, hlam]
                                    · linarith only [h266, h345, hlam]
                                  · linarith only [h0, h344, hlam]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [hlam, p336_0]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h331, hc12, hlam, hphi, ht01, ht0b, ht5b, p336_1, u5ehi3]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h266, h322, h325, hlam, p336_2]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h322, h323, h330, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p336_1]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h322, h330, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p336_1, u3elo2]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h325, hlam, p336_0]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [hlam, p336_0]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                rcases p336_3 (m.d 0 2) (by simp) with h356 | h356
                                · linarith only [h266, h356, hlam]
                                · linarith only [h322, h356, hlam]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h322, h323, h325, h330, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p336_1, u3elo1]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h322, hlam, p336_0]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h326, hlam, p336_0]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h330, hlam, p336_1]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [hlam, p336_0]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h332, hlam, p336_1]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h322, h327, h330, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p336_1]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h327, hlam, p336_0]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [h331, hlam, p336_1]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                rcases p336_3 (m.d 0 2) (by simp) with h368 | h368
                                · linarith only [h323, h368, hlam]
                                · linarith only [h322, h368, hlam]
                              · have p336_0 := h336c.1
                                have p336_1 := h336c.2.1
                                have p336_2 := h336c.2.2.1
                                have p336_3 := h336c.2.2.2
                                linarith only [hlam, p336_0]
                        · linarith only [h266, h322, h330, h331, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h266, h330, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h108, h329, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h266, h322, h325, h328, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h266, h322, h325, h327, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h266, h322, h325, h326, hlam]
            · linarith only [h0, h325, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h379 | h379
          · linarith only [h266, h379, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h381 | h381
            · rcases m.htr 1 2 4 (by decide) (by decide) with h382 | h382
              · rcases m.htr 1 2 5 (by decide) (by decide) with h383 | h383
                · rcases m.htr 1 3 4 (by decide) (by decide) with h384 | h384
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h385 | h385
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h387 | h387
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h388 | h388
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h389 | h389
                            · linarith only [h381, h386, h389, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                            · rcases h2bigk with h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, hlam, p391_1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h266, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h322, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h379, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                rcases p391_3 (m.d 0 2) (by simp) with h397 | h397
                                · linarith only [h0, h397, hlam]
                                · rcases p391_3 (m.d 1 2) (by simp) with h399 | h399
                                  · rcases p391_3 (m.d 2 3) (by simp) with h400 | h400
                                    · linarith only [h381, h400, hlam]
                                    · linarith only [h266, h400, hlam]
                                  · linarith only [h0, h399, hlam]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, h266, hc01, hc12, hlam, hphi, p391_1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h388, h389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p391_1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, h379, hc01, hc12, hlam, hphi, p391_1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p391_1, u3elo2]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h381, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h381, h388, h389, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p391_1, u3elo1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, h379, h381, hc01, hlam, hphi, ht12, ht23, p391_1, u3elo1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, h382, hc01, hc12, hlam, hphi, p391_1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h382, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h386, hlam, p391_1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, h379, h382, h384, hc01, hlam, hphi, ht12, ht23, p391_1, u3elo1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, h383, hc01, hc12, hlam, hphi, p391_1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h383, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h387, hlam, p391_1]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h388, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hlam, p391_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h423 | h423
                            · linarith only [h0, h322, h388, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · rcases h2bigk with h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [hlam, p425_0]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h0, hlam, p425_1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h266, hlam, p425_0]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h322, hlam, p425_0]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h379, hlam, p425_0]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                rcases p425_3 (m.d 0 2) (by simp) with h431 | h431
                                · linarith only [h0, h431, hlam]
                                · rcases p425_3 (m.d 1 2) (by simp) with h433 | h433
                                  · rcases p425_3 (m.d 2 3) (by simp) with h434 | h434
                                    · linarith only [h381, h434, hlam]
                                    · linarith only [h266, h434, hlam]
                                  · linarith only [h0, h433, hlam]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [hlam, p425_0]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h387, hc12, hlam, hphi, ht01, ht0b, ht5b, p425_1, u5ehi3]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h0, h322, hc01, hc12, hlam, hphi, p425_1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h0, h379, hc01, hc12, hlam, hphi, p425_1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p425_1, u3elo2]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h381, hlam, p425_0]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [hlam, p425_0]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h0, h322, h381, hc01, hlam, hphi, ht12, ht23, p425_1, u3elo1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h0, h379, h381, hc01, hlam, hphi, ht12, ht23, p425_1, u3elo1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h0, h388, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p425_1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h382, hlam, p425_0]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h386, hlam, p425_1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [hlam, p425_0]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h388, hlam, p425_1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h0, h383, hc01, hc12, hlam, hphi, p425_1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h383, hlam, p425_0]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h387, hlam, p425_1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [h0, h322, h383, h385, hc01, hlam, hphi, ht12, ht23, p425_1, u3elo1]
                              · have p425_0 := h425c.1
                                have p425_1 := h425c.2.1
                                have p425_2 := h425c.2.2.1
                                have p425_3 := h425c.2.2.2
                                linarith only [hlam, p425_0]
                        · linarith only [h0, h266, h387, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h266, h386, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h108, h385, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h266, h381, h384, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h266, h381, h383, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h266, h381, h382, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h381, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h10, h11, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                          · linarith only [h0, h13, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                            · linarith only [h0, h10, h11, h13, h15, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                              · linarith only [h10, h11, h17, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                                · linarith only [h0, h11, h19, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                · linarith only [h13, h19, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h10, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
                      · linarith only [h23, h9, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                        · linarith only [h2, h25, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                            · linarith only [h0, h28, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h27, h28, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h27, h9, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                        · linarith only [h2, h34, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                          · linarith only [h0, h32, h36, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h36, h6, h8, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h33, h4, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                      · linarith only [h32, h40, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h4, h40, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
                · linarith only [h44, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h46 | h46
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                        · linarith only [h0, h48, h49, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h46, h48, h49, h6, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h47, h48, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h3, h44, h47, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
                        · linarith only [h2, h46, h56, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                          · linarith only [h1, h46, h54, h58, h6, hc45, hlam, hphi, ht34, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                            · linarith only [h55, h58, h60, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                              · linarith only [h0, h46, h55, h6, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                                · linarith only [h1, h46, h54, h6, h64, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h1, h54, h6, h64, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h4, h46, h55, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                    · linarith only [h3, h54, h6, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h71 | h71
          · linarith only [h3, h71, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h73 | h73
            · linarith only [h71, h73, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                    · linarith only [h0, h71, h78, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                      · linarith only [h0, h71, h80, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                        · linarith only [h2, h82, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h3, h75, h77, h80, h82, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
                    · linarith only [h0, h3, h71, h77, h85, hc45, hlam, hphi, ht34, u3ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
                      · linarith only [h0, h71, h77, h87, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                        · linarith only [h2, h71, h77, h89, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h93 | h93
                              · linarith only [h0, h71, h77, h93, hc24, hlam, hphi, u2ehi1]
                              · linarith only [h0, h71, h93, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                            · linarith only [h0, h3, h76, h92, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h3, h76, h91, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · linarith only [h75, h76, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h99 | h99
                · linarith only [h75, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                    · linarith only [h0, h102, h3, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                      · linarith only [h0, h101, h104, h71, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                        · linarith only [h106, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h101, h104, h106, h71, hc24, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
                    · linarith only [h0, h101, h109, h3, h75, hc45, hlam, hphi, ht34, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h111 | h111
                      · linarith only [h0, h101, h111, h3, h75, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                        · linarith only [h101, h113, h2, h3, h75, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                          · linarith only [h0, h115, h3, h75, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h115, h3, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h118 | h118
        · rcases m.htr 0 2 4 (by decide) (by decide) with h119 | h119
          · linarith only [h0, h119, h2, hlam]
          · linarith only [h118, h119, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h122 | h122
          · linarith only [h118, h122, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h124 | h124
            · linarith only [h118, h124, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h126 | h126
              · linarith only [h1, h126, h2, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h128 | h128
                · linarith only [h126, h128, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h130 | h130
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h131 | h131
                    · linarith only [h0, h131, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
                      · linarith only [h1, h122, h130, h131, h133, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · linarith only [h1, h131, h133, h2, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h130, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h137 | h137
      · rcases m.htr 0 2 3 (by decide) (by decide) with h138 | h138
        · linarith only [h0, h1, h138, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h140 | h140
          · linarith only [h138, h140, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h142 | h142
            · linarith only [h1, h137, h140, h142, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h144 | h144
              · rcases m.htr 0 3 5 (by decide) (by decide) with h145 | h145
                · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
                  · linarith only [h1, h137, h146, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
                    · linarith only [h0, h1, h138, h148, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h148, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h145, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h144, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h153 | h153
        · linarith only [h0, h1, h153, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h155 | h155
          · linarith only [h153, h155, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h157 | h157
            · linarith only [h153, h157, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h159 | h159
              · rcases m.htr 0 3 5 (by decide) (by decide) with h160 | h160
                · rcases m.htr 0 4 5 (by decide) (by decide) with h161 | h161
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h162 | h162
                    · linarith only [h0, h1, h153, h162, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h162, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h137, h161, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h159, h160, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h1, h159, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h168 | h168
    · rcases m.htr 0 1 4 (by decide) (by decide) with h169 | h169
      · rcases m.htr 0 2 3 (by decide) (by decide) with h170 | h170
        · rcases m.htr 0 2 4 (by decide) (by decide) with h171 | h171
          · rcases m.htr 0 2 5 (by decide) (by decide) with h172 | h172
            · rcases m.htr 0 3 4 (by decide) (by decide) with h173 | h173
              · rcases m.htr 0 3 5 (by decide) (by decide) with h174 | h174
                · linarith only [h0, h168, h174, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · linarith only [h173, h174, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h177 | h177
                · linarith only [h173, h177, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h179 | h179
                  · linarith only [h0, h169, h179, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h182 | h182
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                        · linarith only [h0, h169, h173, h179, h183, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                          · linarith only [h0, h168, h181, h185, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h187 | h187
                            · linarith only [h168, h172, h173, h177, h181, h187, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h189 | h189
                              · linarith only [h0, h169, h173, h179, h182, h189, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h191 | h191
                                · linarith only [h169, h179, h182, h185, h191, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h168, h173, h181, h191, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h168, h181, h182, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h168, h181, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h170, h172, hc25, hlam, hphi, u2ehi2]
          · linarith only [h170, h171, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h168, h170, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h199 | h199
        · rcases m.htr 0 2 4 (by decide) (by decide) with h200 | h200
          · rcases m.htr 0 2 5 (by decide) (by decide) with h201 | h201
            · rcases m.htr 0 3 4 (by decide) (by decide) with h202 | h202
              · linarith only [h168, h169, h202, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h204 | h204
                · linarith only [h202, h204, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h206 | h206
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h207 | h207
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h209 | h209
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h210 | h210
                          · linarith only [h168, h169, h202, h207, h208, h210, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
                            · linarith only [h168, h204, h207, h212, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h214 | h214
                              · linarith only [h200, h214, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h202, h206, h214, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h169, h202, h206, h209, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h168, h207, h208, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h168, h207, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h168, h169, h206, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h199, h201, hc25, hlam, hphi, u2ehi2]
          · linarith only [h199, h200, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h168, h199, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h224 | h224
      · rcases m.htr 0 2 3 (by decide) (by decide) with h225 | h225
        · rcases m.htr 0 2 4 (by decide) (by decide) with h226 | h226
          · rcases m.htr 0 2 5 (by decide) (by decide) with h227 | h227
            · rcases m.htr 0 3 4 (by decide) (by decide) with h228 | h228
              · rcases m.htr 0 3 5 (by decide) (by decide) with h229 | h229
                · rcases m.htr 0 4 5 (by decide) (by decide) with h230 | h230
                  · linarith only [h0, h224, h230, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h233 | h233
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
                        · linarith only [h168, h224, h230, h232, h234, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h237 | h237
                            · linarith only [h225, h237, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h229, h236, h237, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h228, h230, h236, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h168, h229, h232, h233, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h224, h226, h232, hc23, hlam, hphi, u2ehi3]
                · linarith only [h228, h229, hc35, hlam, hphi, u3ehi3]
              · linarith only [h168, h224, h228, hlam]
            · linarith only [h225, h227, hc25, hlam, hphi, u2ehi2]
          · linarith only [h225, h226, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h247 | h247
          · linarith only [h225, h247, hc23, hlam, hphi, u2ehi3]
          · linarith only [h0, h224, h247, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h250 | h250
        · rcases m.htr 0 2 4 (by decide) (by decide) with h251 | h251
          · rcases m.htr 0 2 5 (by decide) (by decide) with h252 | h252
            · rcases m.htr 0 3 4 (by decide) (by decide) with h253 | h253
              · rcases m.htr 0 3 5 (by decide) (by decide) with h254 | h254
                · rcases m.htr 0 4 5 (by decide) (by decide) with h255 | h255
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h256 | h256
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h257 | h257
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h258 | h258
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h259 | h259
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                            · linarith only [h250, h260, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h0, h250, h254, h259, h260, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h263 | h263
                            · linarith only [h259, h263, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h265 | h265
                              · linarith only [h0, h251, h265, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h267 | h267
                                · linarith only [h0, h250, h253, h259, h265, h267, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h255, h259, h267, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h224, h250, h253, h255, h258, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h250, h253, h255, h257, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h250, h253, h255, h256, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h273 | h273
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h274 | h274
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h275 | h275
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                            · linarith only [h250, h277, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h254, h255, h274, h275, h276, h277, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h253, h255, h274, h275, h276, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
                            · linarith only [h0, h250, h282, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h0, h250, h254, h281, h282, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h224, h253, h275, h281, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h251, h255, h274, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h0, h250, h254, h273, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h253, h254, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
                · linarith only [h253, h289, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h294 | h294
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h295 | h295
                          · linarith only [h250, h253, h295, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
                            · linarith only [h0, h250, h297, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h299 | h299
                              · linarith only [h0, h251, h299, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · linarith only [h253, h291, h299, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h224, h291, h294, hlam]
                      · linarith only [h0, h250, h293, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h251, h291, h292, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h305 | h305
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h306 | h306
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h307 | h307
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                          · linarith only [h250, h253, h291, h306, h307, h308, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h310 | h310
                            · linarith only [h250, h289, h310, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
                              · linarith only [h251, h291, h312, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h314 | h314
                                · linarith only [h250, h253, h291, h314, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h250, h253, h306, h307, h314, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
                          · linarith only [h250, h253, h317, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h319 | h319
                            · linarith only [h250, h289, h319, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h321 | h321
                              · linarith only [h224, h307, h321, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h323 | h323
                                · linarith only [h224, h307, h323, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h253, h323, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h0, h250, h306, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h250, h252, h253, h291, h305, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
            · linarith only [h250, h252, hc25, hlam, hphi, u2ehi2]
          · linarith only [h250, h251, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h330 | h330
          · linarith only [h250, h330, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h332 | h332
            · linarith only [h250, h332, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h334 | h334
              · rcases m.htr 0 3 5 (by decide) (by decide) with h335 | h335
                · rcases m.htr 0 4 5 (by decide) (by decide) with h336 | h336
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
                    · linarith only [h250, h334, h336, h337, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h339 | h339
                      · linarith only [h330, h337, h339, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h341 | h341
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h342 | h342
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h344 | h344
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
                                · linarith only [h168, h334, h337, h345, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                · rcases h0bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h0, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h168, hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h224, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht0b, ht5b, p347_1, u5ehi0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h0, h339, h342, hc01, hc23, hlam, hphi, ht12, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h250, hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h330, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h332, hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    rcases p347_3 (m.d 0 1) (by simp) with h358 | h358
                                    · linarith only [h168, h358, hlam]
                                    · rcases p347_3 (m.d 0 2) (by simp) with h360 | h360
                                      · linarith only [h250, h360, hlam]
                                      · linarith only [h0, h360, hlam]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h168, h337, hc23, hlam, hphi, p347_1, u2ehi0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h168, h336, h337, h345, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p347_1, u3ehi3]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h168, h337, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p347_1, u5ehi0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    rcases p347_3 (m.d 0 1) (by simp) with h367 | h367
                                    · linarith only [h224, h367, hlam]
                                    · rcases p347_3 (m.d 0 2) (by simp) with h369 | h369
                                      · linarith only [h330, h369, hlam]
                                      · linarith only [h0, h369, hlam]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h224, h339, h342, hc23, hlam, hphi, p347_1, u2ehi0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h334, hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h224, h336, h339, h342, h345, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p347_1, u3ehi3]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    rcases p347_3 (m.d 0 1) (by simp) with h376 | h376
                                    · linarith only [h376, hlam, p347_0]
                                    · rcases p347_3 (m.d 0 2) (by simp) with h378 | h378
                                      · linarith only [h332, h378, hlam]
                                      · linarith only [h0, h378, hlam]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h332, hc25, hlam, hphi, p347_1, u2ehi0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h335, hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h336, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hlam, p347_0]
                              · linarith only [h339, h344, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                            · linarith only [h339, h342, h343, hc35, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h168, h334, h336, h337, h342, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h224, h336, h341, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
                    · linarith only [h250, h335, h389, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
                      · linarith only [h330, h389, h391, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h393 | h393
                        · linarith only [h330, h336, h391, h393, hc24, hlam, hphi, u2ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h395 | h395
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h396 | h396
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h397 | h397
                              · linarith only [h224, h393, h395, h397, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h330, h397, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h168, h250, h335, h396, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h168, h335, h389, h395, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · linarith only [h334, h335, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h403 | h403
                · linarith only [h334, h403, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h405 | h405
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
                      · linarith only [h330, h405, h407, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · linarith only [h250, h406, h407, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h410 | h410
                      · linarith only [h406, h410, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h413 | h413
                          · linarith only [h250, h334, h413, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h406, h413, hc34, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h224, h405, h412, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h419 | h419
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h420 | h420
                          · linarith only [h250, h334, h417, h420, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h250, h420, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h330, h418, h419, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h250, h417, h418, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h425 | h425
                      · linarith only [h417, h425, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h427 | h427
                        · linarith only [h330, h405, h425, h427, hc24, hlam, hphi, u2ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h429 | h429
                          · linarith only [h250, h334, h429, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h250, h429, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
