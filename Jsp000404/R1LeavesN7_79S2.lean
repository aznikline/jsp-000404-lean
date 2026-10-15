import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_0_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h1, h12, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                          · linarith only [h12, h6, h9, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                        · linarith only [h11, h2, h5, h9, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                      · linarith only [h1, h10, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h17, h9, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1, h17, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                  · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
                · linarith only [h6, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h1, h6, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
              · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h0, h28, h5, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                          · linarith only [h1, h30, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                          · linarith only [h23, h26, h30, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                      · linarith only [h1, h27, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                      · linarith only [h26, h34, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1, h34, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                  · linarith only [h25, h3, hc12, hlam, hphi, u2elo0]
                · linarith only [h23, h24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h1, h23, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
            · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
              · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                      · linarith only [h4, h41, h45, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                      · linarith only [h44, h45, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                      · linarith only [h44, h48, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                          · linarith only [h44, h51, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                            · linarith only [h1, h4, h53, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h55 | h55
                              · linarith only [h2, h55, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                              · linarith only [h2, h40, h51, h55, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                        · linarith only [h2, h40, h41, h44, h50, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                  · linarith only [h3, h43, hc12, hlam, hphi, u2elo0]
                · linarith only [h41, h42, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h1, h41, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
              · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
                · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h66 | h66
                      · linarith only [h1, h4, h62, h66, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                      · linarith only [h65, h66, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h69 | h69
                      · linarith only [h65, h69, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h71 | h71
                        · linarith only [h0, h40, h71, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                          · linarith only [h1, h4, h73, hc35, hlam, hphi, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                            · linarith only [h1, h4, h75, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
                              · linarith only [h2, h77, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                                · linarith only [h65, h71, h79, hc34, hlam, hphi, u3ehi1]
                                · linarith only [h62, h65, h79, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h3, h64, hc12, hlam, hphi, u2elo0]
                · linarith only [h62, h63, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h1, h62, hc12, hlam, hphi, u2elo0]
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h87 | h87
      · rcases m.htr 0 2 5 (by decide) (by decide) with h88 | h88
        · linarith only [h1, h88, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h90 | h90
          · rcases m.htr 0 4 5 (by decide) (by decide) with h91 | h91
            · linarith only [h1, h87, h91, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
              · linarith only [h1, h93, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                  · linarith only [h87, h88, h93, h96, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h100 | h100
                        · linarith only [h100, h91, h93, h95, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                          · linarith only [h1, h102, h87, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                          · linarith only [h1, h102, h87, h98, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1, h90, h99, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                    · linarith only [h93, h95, h98, hlam]
                · linarith only [h87, h88, h95, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
            · linarith only [h108, h87, h88, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
              · linarith only [h1, h110, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
                · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                  · linarith only [h110, h113, h88, h90, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                      · linarith only [h110, h116, h90, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                      · linarith only [h115, h116, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h110, h112, h115, hlam]
                · linarith only [h112, h87, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h121 | h121
        · linarith only [h1, h121, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h123 | h123
          · rcases m.htr 0 4 5 (by decide) (by decide) with h124 | h124
            · rcases m.htr 1 2 3 (by decide) (by decide) with h125 | h125
              · linarith only [h1, h125, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                · linarith only [h124, h125, h127, h87, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                  · linarith only [h121, h125, h129, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h132 | h132
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h133 | h133
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h135 | h135
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h136 | h136
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h137 | h137
                                · linarith only [h125, h131, h137, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                                · linarith only [h124, h134, h137, h87, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                              · linarith only [h124, h136, h87, hlam]
                            · linarith only [h123, h124, h134, h135, h87, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h1, h123, h131, h134, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h124, h127, h133, h87, hc12, hlam, hphi, u2elo3]
                      · linarith only [h1, h123, h132, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h145 | h145
                      · linarith only [h131, h145, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1, h123, h145, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
              · linarith only [h1, h123, h148, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h150 | h150
                · linarith only [h148, h150, h87, hc02, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
                  · linarith only [h0, h121, h150, h152, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                        · linarith only [h124, h150, h156, h87, hc02, hlam, hphi, u2elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h159 | h159
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                              · linarith only [h124, h158, h160, h87, hc02, hlam, hphi, u2elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h162 | h162
                                · linarith only [h1, h123, h150, h154, h160, h162, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u2elo2, u3ehi4]
                                · rcases h5bigk with h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [hlam, p164_0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h1, h123, hlam, hphi, ht01, ht0b, ht12, ht5b, p164_1, u2elo2, u5ehi1]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h121, hlam, p164_0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h1, h123, h162, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p164_1, u2elo2, u3ehi3]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h124, hlam, p164_1]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h0, hlam, p164_0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [hlam, p164_0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h152, hlam, p164_0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h0, h162, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p164_1, u3ehi3]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h156, hlam, p164_1]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h159, hlam, hphi, ht01, ht0b, ht12, ht5b, p164_1, u2elo2, u5ehi0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h159, hlam, hphi, ht01, ht0b, ht12, ht5b, p164_1, u2elo2, u5ehi1]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [hlam, p164_0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h159, h162, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p164_1, u2elo2, u3ehi3]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h160, hlam, p164_1]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h123, hlam, p164_0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h155, hlam, p164_0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h159, hlam, p164_0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [hlam, p164_0]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h162, hlam, p164_1]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h0, h155, h162, hc45, hlam, hphi, ht34, p164_1, u3ehi3]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h155, h162, hc45, hlam, hphi, ht34, p164_1, u3ehi3]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h121, hc02, hc45, hlam, hphi, ht23, ht34, p164_1]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [h162, hc45, hlam, hphi, ht34, p164_1, u3ehi3]
                                  · have p164_0 := h164c.1
                                    have p164_1 := h164c.2.1
                                    have p164_2 := h164c.2.2.1
                                    have p164_3 := h164c.2.2.2
                                    linarith only [hlam, p164_0]
                            · linarith only [h1, h123, h159, hlam]
                          · linarith only [h0, h1, h121, h123, h154, h156, h158, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                      · linarith only [h123, h154, h155, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                      · linarith only [h154, h193, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1, h123, h193, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h196 | h196
            · rcases m.htr 1 2 3 (by decide) (by decide) with h197 | h197
              · linarith only [h1, h197, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
                · linarith only [h123, h196, h197, h199, h87, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                  · linarith only [h197, h201, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h203 | h203
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
                      · linarith only [h123, h197, h204, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                      · linarith only [h203, h204, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h207 | h207
                      · linarith only [h203, h207, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h209 | h209
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h210 | h210
                          · linarith only [h197, h203, h210, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
                            · linarith only [h207, h212, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h214 | h214
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h215 | h215
                                · rcases h5bigk with h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h121, h207, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p216_1, u2elo4, u3ehi1]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h121, hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h123, hlam, p216_1]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h196, h87, hlam, hphi, ht01, ht0b, ht12, ht5b, p216_1, u2elo3, u5ehi4]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h0, hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h201, hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h207, hlam, p216_1]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p216_1, u5ehi4]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p216_1, u2elo4, u5ehi0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p216_1, u2elo4, u5ehi1]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h212, hlam, p216_1]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h214, hlam, hphi, ht01, ht0b, ht12, ht5b, p216_1, u2elo3, u5ehi4]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h0, h207, h215, hc34, hlam, hphi, p216_1, u3ehi1]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h207, h215, hc34, hlam, hphi, p216_1, u3ehi1]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h121, h215, hc02, hc34, hlam, hphi, ht23, p216_1]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    rcases p216_3 (m.d 0 5) (by simp) with h236 | h236
                                    · linarith only [h123, h236, hlam]
                                    · linarith only [h196, h236, hlam]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h196, hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h209, hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h214, hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [h215, hlam, p216_0]
                                  · have p216_0 := h216c.1
                                    have p216_1 := h216c.2.1
                                    have p216_2 := h216c.2.2.1
                                    have p216_3 := h216c.2.2.2
                                    linarith only [hlam, p216_0]
                                · linarith only [h196, h215, h87, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                              · linarith only [h0, h121, h209, h214, h87, hc02, hlam, hphi, u2elo4]
                        · linarith only [h196, h199, h209, h87, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h247 | h247
              · linarith only [h1, h247, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h249 | h249
                · linarith only [h247, h249, h87, hc02, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h251 | h251
                  · linarith only [h121, h247, h251, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h254 | h254
                      · linarith only [h123, h247, h254, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                      · linarith only [h253, h254, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h257 | h257
                      · linarith only [h253, h257, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h259 | h259
                        · linarith only [h196, h249, h259, h87, hc02, hlam, hphi, u2elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h261 | h261
                          · linarith only [h247, h253, h261, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h263 | h263
                            · linarith only [h257, h261, h263, hc34, hlam, hphi, u3ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h265 | h265
                              · linarith only [h196, h265, h87, hc02, hlam, hphi, u2elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h267 | h267
                                · linarith only [h247, h261, h265, h267, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h253, h267, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h270 | h270
    · rcases m.htr 0 2 4 (by decide) (by decide) with h271 | h271
      · rcases m.htr 0 2 5 (by decide) (by decide) with h272 | h272
        · rcases m.htr 0 3 5 (by decide) (by decide) with h273 | h273
          · rcases m.htr 0 4 5 (by decide) (by decide) with h274 | h274
            · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
              · rcases m.htr 1 2 4 (by decide) (by decide) with h276 | h276
                · rcases m.htr 1 2 5 (by decide) (by decide) with h277 | h277
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                          · linarith only [h270, h281, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                          · linarith only [h275, h278, h281, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                        · linarith only [h271, h274, h278, h280, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                      · linarith only [h270, h273, h279, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h286 | h286
                      · linarith only [h278, h286, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h270, h273, h286, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                  · linarith only [h272, h277, hc12, hlam, hphi, u2elo0]
                · linarith only [h275, h276, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h270, h275, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
              · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
                · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h296 | h296
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h297 | h297
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h298 | h298
                          · linarith only [h270, h298, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                          · linarith only [h292, h295, h298, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
                          · linarith only [h270, h301, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                          · linarith only [h295, h297, h301, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h273, h295, h296, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h305 | h305
                      · linarith only [h295, h305, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h270, h273, h305, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                  · linarith only [h272, h294, hc12, hlam, hphi, u2elo0]
                · linarith only [h292, h293, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h270, h292, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h311 | h311
            · rcases m.htr 1 2 3 (by decide) (by decide) with h312 | h312
              · rcases m.htr 1 2 4 (by decide) (by decide) with h313 | h313
                · rcases m.htr 1 2 5 (by decide) (by decide) with h314 | h314
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h315 | h315
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h316 | h316
                      · linarith only [h273, h312, h316, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                      · linarith only [h315, h316, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h319 | h319
                      · linarith only [h315, h319, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                          · linarith only [h315, h322, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h324 | h324
                            · linarith only [h0, h319, h324, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h326 | h326
                              · linarith only [h271, h326, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                              · linarith only [h271, h311, h322, h326, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                        · linarith only [h271, h311, h312, h315, h321, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                  · linarith only [h272, h314, hc12, hlam, hphi, u2elo0]
                · linarith only [h312, h313, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h270, h312, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h333 | h333
              · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
                · rcases m.htr 1 2 5 (by decide) (by decide) with h335 | h335
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h337 | h337
                      · linarith only [h270, h273, h333, h337, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                      · linarith only [h336, h337, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h340 | h340
                      · linarith only [h336, h340, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h342 | h342
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h343 | h343
                          · linarith only [h270, h273, h311, h336, h342, h343, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h271, h311, h334, h342, h343, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h346 | h346
                          · linarith only [h333, h336, h346, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h348 | h348
                            · linarith only [h333, h336, h348, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h350 | h350
                              · linarith only [h271, h336, h342, h350, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h352 | h352
                                · linarith only [h271, h311, h346, h352, hc34, hlam, hphi, u3ehi2]
                                · linarith only [h333, h336, h352, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h272, h335, hc12, hlam, hphi, u2elo0]
                · linarith only [h333, h334, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h270, h333, hc12, hlam, hphi, u2elo0]
        · linarith only [h270, h272, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · linarith only [h270, h271, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h360 | h360
      · rcases m.htr 0 2 5 (by decide) (by decide) with h361 | h361
        · linarith only [h270, h361, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h363 | h363
          · rcases m.htr 0 4 5 (by decide) (by decide) with h364 | h364
            · linarith only [h270, h360, h364, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h366 | h366
              · linarith only [h270, h366, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h368 | h368
                · rcases m.htr 1 2 5 (by decide) (by decide) with h369 | h369
                  · linarith only [h360, h361, h366, h369, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h372 | h372
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h373 | h373
                        · linarith only [h364, h366, h368, h373, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h375 | h375
                          · linarith only [h270, h360, h375, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                          · linarith only [h270, h360, h371, h375, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h270, h363, h372, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                    · linarith only [h366, h368, h371, hlam]
                · linarith only [h360, h368, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h381 | h381
            · linarith only [h360, h361, h381, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h383 | h383
              · linarith only [h270, h383, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h385 | h385
                · rcases m.htr 1 2 5 (by decide) (by decide) with h386 | h386
                  · linarith only [h383, h386, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h389 | h389
                      · linarith only [h363, h383, h389, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                      · linarith only [h388, h389, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h383, h385, h388, hlam]
                · linarith only [h360, h385, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h394 | h394
        · linarith only [h270, h394, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h396 | h396
          · rcases m.htr 0 4 5 (by decide) (by decide) with h397 | h397
            · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
              · linarith only [h270, h398, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h400 | h400
                · linarith only [h360, h397, h398, h400, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h402 | h402
                  · linarith only [h394, h400, h402, hc02, hlam, hphi, u2elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h404 | h404
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h405 | h405
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h406 | h406
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h407 | h407
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h408 | h408
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h409 | h409
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h410 | h410
                                · linarith only [h398, h404, h410, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                                · linarith only [h360, h397, h407, h410, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                              · linarith only [h360, h397, h409, hlam]
                            · linarith only [h360, h396, h397, h407, h408, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h270, h396, h404, h407, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h360, h397, h400, h406, hc12, hlam, hphi, u2elo3]
                      · linarith only [h396, h404, h405, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
                      · linarith only [h404, h418, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h270, h396, h418, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
              · linarith only [h270, h396, h421, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                · linarith only [h360, h421, h423, hc02, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h425 | h425
                  · linarith only [h394, h423, h425, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h428 | h428
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h429 | h429
                        · linarith only [h360, h397, h423, h429, hc02, hlam, hphi, u2elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h431 | h431
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h432 | h432
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h433 | h433
                              · linarith only [h360, h397, h431, h433, hc02, hlam, hphi, u2elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h435 | h435
                                · linarith only [h423, h427, h433, h435, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h5bigk with h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h0, hlam, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h394, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h0, h425, h435, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p437_1, u2elo4, u3ehi3]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h397, hlam, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h425, hlam, hphi, ht01, ht0b, ht12, ht5b, p437_1, u2elo4, u5ehi0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h425, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h421, h428, h435, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p437_1, u2elo2, u3ehi3]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h429, hlam, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h396, h435, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p437_1, u2elo4, u3ehi3]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p437_1, u2elo4, u5ehi1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h432, h435, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p437_1, u2elo2, u3ehi3]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h433, hlam, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h396, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h428, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h432, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h435, hlam, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h396, h435, hc45, hlam, hphi, ht34, p437_1, u3ehi3]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h270, h394, h396, h435, hc02, hc45, hlam, hphi, ht34, p437_1, u2elo2, u3ehi3]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h435, hc45, hlam, hphi, ht34, p437_1, u3ehi3]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, p437_0]
                            · linarith only [h270, h396, h432, hlam]
                          · linarith only [h270, h396, h431, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h270, h396, h427, h428, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h466 | h466
                      · linarith only [h427, h466, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h270, h396, h466, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h469 | h469
            · rcases m.htr 1 2 3 (by decide) (by decide) with h470 | h470
              · linarith only [h270, h470, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h472 | h472
                · linarith only [h360, h396, h469, h470, h472, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h474 | h474
                  · linarith only [h470, h474, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h476 | h476
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
                      · linarith only [h396, h470, h477, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                      · linarith only [h476, h477, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h480 | h480
                      · linarith only [h476, h480, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h482 | h482
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                          · linarith only [h476, h483, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h485 | h485
                            · linarith only [h470, h480, h483, h485, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h488 | h488
                                · rcases h5bigk with h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h0, hlam, p489_1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h394, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h396, hlam, p489_1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h394, h487, hlam, hphi, ht01, ht0b, ht12, ht5b, p489_1, u2elo3, u5ehi4]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h474, h487, hlam, hphi, ht01, ht0b, ht12, ht5b, p489_1, u2elo3, u5ehi0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h474, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h480, hlam, p489_1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h474, h487, hlam, hphi, ht01, ht0b, ht12, ht5b, p489_1, u2elo3, u5ehi4]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h396, h487, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p489_1, u2elo3, u3ehi0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h487, hlam, hphi, ht01, ht0b, ht12, ht5b, p489_1, u2elo3, u5ehi1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h485, hlam, p489_1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h487, hlam, hphi, ht01, ht0b, ht12, ht5b, p489_1, u2elo3, u5ehi4]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h396, hc35, hlam, hphi, p489_1, u3ehi0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p489_1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h394, hc02, hc35, hlam, hphi, ht23, p489_1]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    rcases p489_3 (m.d 0 5) (by simp) with h509 | h509
                                    · linarith only [h396, h509, hlam]
                                    · linarith only [h469, h509, hlam]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h469, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h482, hlam, p489_0]
                                  · have p489_0 := h489c.1
                                    have p489_1 := h489c.2.1
                                    have p489_2 := h489c.2.2.1
                                    have p489_3 := h489c.2.2.2
                                    linarith only [h487, hlam, p489_0]
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
                                · linarith only [h360, h469, h488, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                              · linarith only [h360, h469, h487, hlam]
                        · linarith only [h360, h469, h472, h482, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h520 | h520
              · linarith only [h270, h520, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h522 | h522
                · linarith only [h360, h520, h522, hc02, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h524 | h524
                  · linarith only [h522, h524, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h526 | h526
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
                      · linarith only [h396, h520, h527, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                      · linarith only [h526, h527, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h530 | h530
                      · linarith only [h526, h530, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h532 | h532
                        · linarith only [h360, h469, h522, h532, hc02, hlam, hphi, u2elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h534 | h534
                          · linarith only [h526, h534, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h536 | h536
                            · linarith only [h530, h534, h536, hc34, hlam, hphi, u3ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h538 | h538
                              · linarith only [h360, h469, h538, hc02, hlam, hphi, u2elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h540 | h540
                                · linarith only [h526, h532, h540, hc34, hlam, hphi, u3ehi1]
                                · linarith only [h526, h540, hc45, hlam, hphi, ht34, u3ehi1]

end R2N4
