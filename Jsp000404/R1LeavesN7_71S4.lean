import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_0_L_I_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                    · linarith only [h0, h5, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h0, h14, h4, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h16, h4, h8, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                          · linarith only [h0, h12, h16, h18, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h0, h12, h20, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                            · linarith only [h0, h20, h5, h7, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                    · linarith only [h0, h24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                    · linarith only [h0, h23, h24, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                    · linarith only [h0, h27, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                      · linarith only [h0, h23, h29, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                        · linarith only [h0, h23, h31, h4, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                          · linarith only [h0, h27, h31, h33, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                            · linarith only [h0, h27, h35, h5, h7, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                              · linarith only [h0, h31, h37, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                                · linarith only [h0, h33, h35, h37, h39, h5, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                                  · linarith only [h41, h5, h7, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                                    · linarith only [h23, h37, h43, h5, h7, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h23, h37, h43, hc12, hc45, hlam, hphi, ht23, ht34]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h46 | h46
                · linarith only [h46, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                    · linarith only [h0, h49, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                    · linarith only [h49, h5, h6, hc12, hc25, hlam, hphi]
                  · linarith only [h4, h48, h6, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h53 | h53
              · rcases m.htr 0 4 5 (by decide) (by decide) with h54 | h54
                · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
                    · linarith only [h5, h53, h56, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
                      · linarith only [h2, h56, h58, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                      · linarith only [h5, h53, h58, hc12, hc24, hlam, hphi]
                  · linarith only [h4, h5, h55, hc12, hc24, hlam, hphi]
                · linarith only [h5, h53, h54, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h63 | h63
                · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
                    · linarith only [h0, h65, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h67 | h67
                      · linarith only [h2, h65, h67, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h69 | h69
                        · linarith only [h1, h69, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                          · linarith only [h2, h64, h65, h71, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                            · linarith only [h2, h73, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                            · linarith only [h2, h63, h73, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
                  · linarith only [h4, h5, h64, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                    · linarith only [h0, h5, h78, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                      · linarith only [h0, h53, h80, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                        · linarith only [h1, h82, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                          · linarith only [h2, h77, h78, h84, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                            · linarith only [h2, h86, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                              · linarith only [h3, h77, h78, h82, h86, h88, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                                · linarith only [h1, h77, h84, h86, h90, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                                  · linarith only [h0, h5, h63, h77, h88, h92, hc23, hc34, hlam, hphi]
                                  · linarith only [h0, h5, h77, h92, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h4, h5, h77, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h96 | h96
            · rcases m.htr 0 2 5 (by decide) (by decide) with h97 | h97
              · rcases m.htr 0 4 5 (by decide) (by decide) with h98 | h98
                · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
                  · linarith only [h4, h96, h99, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                    · linarith only [h1, h101, h99, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                    · linarith only [h101, h4, h96, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
                  · linarith only [h104, h4, h96, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                    · linarith only [h1, h104, h106, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                    · linarith only [h106, h4, h96, hc12, hc23, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h109 | h109
                · linarith only [h109, h96, h97, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                  · linarith only [h111, h4, h96, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                    · linarith only [h1, h111, h113, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                    · linarith only [h113, h4, h96, hc12, hc23, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h116 | h116
              · rcases m.htr 0 4 5 (by decide) (by decide) with h117 | h117
                · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                  · linarith only [h116, h118, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
                    · linarith only [h1, h116, h118, h120, h96, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                      · linarith only [h1, h118, h122, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                      · linarith only [h116, h122, h4, hc12, hc23, hlam, hphi]
                · linarith only [h116, h117, h96, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                  · linarith only [h0, h127, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                    · linarith only [h126, h129, h96, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                      · linarith only [h1, h116, h127, h131, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                        · linarith only [h1, h133, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                          · linarith only [h133, h135, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                            · linarith only [h137, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                            · linarith only [h126, h137, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
                  · linarith only [h0, h140, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
                    · linarith only [h0, h142, h96, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                      · linarith only [h0, h116, h144, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                        · linarith only [h1, h146, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h148 | h148
                          · linarith only [h146, h148, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                            · linarith only [h126, h150, h2, h96, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h153 | h153
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h155 | h155
                                    · linarith only [h126, h152, h155, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                                    · linarith only [h140, h146, h152, h154, h155, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                                    · linarith only [h0, h154, h158, h96, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h2bigk with h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h4, hc12, hc23, hlam, hphi, p160_1]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h4, hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h96, hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h116, hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h0, hlam, p160_1]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h140, hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h142, hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h144, hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        rcases p160_3 (m.d 0 2) (by simp) with h171 | h171
                                        · linarith only [h171, hlam, p160_0]
                                        · rcases p160_3 (m.d 1 2) (by simp) with h173 | h173
                                          · linarith only [h140, h173, hlam]
                                          · rcases p160_3 (m.d 2 3) (by simp) with h175 | h175
                                            · rcases p160_3 (m.d 2 4) (by simp) with h176 | h176
                                              · linarith only [h152, h176, hlam]
                                              · linarith only [h176, h96, hlam]
                                            · linarith only [h175, hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        rcases p160_3 (m.d 0 2) (by simp) with h180 | h180
                                        · linarith only [h180, h4, hlam]
                                        · linarith only [h0, h180, hlam]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h140, h146, h152, hc12, hc23, hlam, hphi, p160_1]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h116, hc02, hc23, hlam, hphi, p160_1]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h0, h154, hc12, hc45, hlam, hphi, ht23, ht34, p160_1]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h154, hc12, hc45, hlam, hphi, ht23, ht34, p160_1]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h152, hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h154, hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        rcases p160_3 (m.d 0 2) (by simp) with h191 | h191
                                        · linarith only [h191, hlam, p160_0]
                                        · rcases p160_3 (m.d 1 2) (by simp) with h193 | h193
                                          · linarith only [h144, h193, hlam]
                                          · rcases p160_3 (m.d 2 3) (by simp) with h195 | h195
                                            · rcases p160_3 (m.d 2 4) (by simp) with h196 | h196
                                              · linarith only [h154, h196, hlam]
                                              · linarith only [h196, h96, hlam]
                                            · linarith only [h195, h4, hlam]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        rcases p160_3 (m.d 0 2) (by simp) with h200 | h200
                                        · linarith only [h116, h200, hlam]
                                        · linarith only [h0, h200, hlam]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h153, hlam, p160_0]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [h0, h96, hc12, hc25, hlam, hphi, p160_1]
                                      · have p160_0 := h160c.1
                                        have p160_1 := h160c.2.1
                                        have p160_2 := h160c.2.2.1
                                        have p160_3 := h160c.2.2.2
                                        linarith only [hlam, p160_0]
                                · linarith only [h140, h146, h152, h153, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h207 | h207
                                · linarith only [h140, h148, h152, h207, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                                    · rcases h2bigk with h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h207, h210, h4, hc12, hc34, hlam, hphi, ht23, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h4, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h96, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h116, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h0, hlam, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h140, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h142, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h144, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h207, h210, hc02, hc34, hlam, hphi, ht23, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h207, h210, hc12, hc34, hlam, hphi, ht23, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h152, hlam, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h207, hlam, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        rcases p211_3 (m.d 0 2) (by simp) with h227 | h227
                                        · linarith only [h227, hlam, p211_0]
                                        · rcases p211_3 (m.d 1 2) (by simp) with h229 | h229
                                          · linarith only [h142, h229, hlam]
                                          · rcases p211_3 (m.d 2 3) (by simp) with h231 | h231
                                            · linarith only [h152, h231, hlam]
                                            · linarith only [h231, h4, hlam]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        rcases p211_3 (m.d 0 2) (by simp) with h234 | h234
                                        · linarith only [h234, h96, hlam]
                                        · linarith only [h0, h234, hlam]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h0, h152, h4, hc12, hc34, hlam, hphi, ht23, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h0, h116, h152, hc12, hc34, hlam, hphi, ht23, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        rcases p211_3 (m.d 0 2) (by simp) with h240 | h240
                                        · linarith only [h240, hlam, p211_0]
                                        · rcases p211_3 (m.d 1 2) (by simp) with h242 | h242
                                          · linarith only [h144, h242, hlam]
                                          · rcases p211_3 (m.d 2 3) (by simp) with h244 | h244
                                            · linarith only [h207, h244, hlam]
                                            · linarith only [h244, h4, hlam]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        rcases p211_3 (m.d 0 2) (by simp) with h247 | h247
                                        · linarith only [h116, h247, hlam]
                                        · linarith only [h0, h247, hlam]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h209, hlam, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hlam, p211_0]
                                    · linarith only [h152, h209, h210, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h254 | h254
                                    · linarith only [h0, h209, h254, h96, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h152, h254, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h258 | h258
        · linarith only [h2, h258, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h260 | h260
          · rcases m.htr 0 2 4 (by decide) (by decide) with h261 | h261
            · linarith only [h0, h2, h261, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h263 | h263
              · linarith only [h0, h2, h263, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h265 | h265
                · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
                  · linarith only [h0, h2, h266, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h260, h266, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                  · linarith only [h0, h2, h269, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h260, h269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h272 | h272
            · linarith only [h0, h2, h272, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h274 | h274
              · linarith only [h1, h2, h260, h274, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h276 | h276
                · rcases m.htr 1 2 3 (by decide) (by decide) with h277 | h277
                  · linarith only [h0, h2, h260, h277, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h279 | h279
                    · linarith only [h272, h276, h279, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h281 | h281
                      · linarith only [h1, h2, h274, h277, h281, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h283 | h283
                        · linarith only [h1, h2, h283, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h285 | h285
                          · linarith only [h1, h2, h285, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h287 | h287
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h288 | h288
                              · linarith only [h0, h258, h283, h287, h288, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h290 | h290
                                · linarith only [h1, h258, h277, h285, h288, h290, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h292 | h292
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h293 | h293
                                    · rcases h2bigk with h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [hlam, p294_0]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h0, h258, h287, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p294_1, u1elo3]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h260, hlam, p294_0]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h272, hlam, p294_0]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h274, hlam, p294_0]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h0, hlam, p294_1]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [hlam, p294_0]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h277, hlam, p294_0]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h279, hlam, p294_0]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h281, hlam, p294_0]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h290, h293, hc02, hc34, hlam, hphi, ht23, p294_1]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h290, h293, hc12, hc34, hlam, hphi, ht23, p294_1]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [hlam, p294_0]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h288, hlam, p294_1]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h290, hlam, p294_1]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        rcases p294_3 (m.d 0 2) (by simp) with h310 | h310
                                        · linarith only [h310, hlam, p294_0]
                                        · rcases p294_3 (m.d 1 2) (by simp) with h312 | h312
                                          · linarith only [h279, h312, hlam]
                                          · rcases p294_3 (m.d 2 3) (by simp) with h314 | h314
                                            · linarith only [h288, h314, hlam]
                                            · linarith only [h260, h314, hlam]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        rcases p294_3 (m.d 0 2) (by simp) with h317 | h317
                                        · linarith only [h272, h317, hlam]
                                        · linarith only [h0, h317, hlam]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h0, h260, hc12, hc24, hlam, hphi, p294_1]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [hlam, p294_0]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h258, h281, h288, hc01, hc34, hlam, hphi, ht12, ht23, p294_1]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        rcases p294_3 (m.d 0 2) (by simp) with h323 | h323
                                        · linarith only [h323, hlam, p294_0]
                                        · rcases p294_3 (m.d 1 2) (by simp) with h325 | h325
                                          · linarith only [h281, h325, hlam]
                                          · rcases p294_3 (m.d 2 3) (by simp) with h327 | h327
                                            · linarith only [h290, h327, hlam]
                                            · linarith only [h260, h327, hlam]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        rcases p294_3 (m.d 0 2) (by simp) with h330 | h330
                                        · linarith only [h274, h330, hlam]
                                        · linarith only [h0, h330, hlam]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h0, h260, hc12, hc25, hlam, hphi, p294_1]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [h292, hlam, p294_1]
                                      · have p294_0 := h294c.1
                                        have p294_1 := h294c.2.1
                                        have p294_2 := h294c.2.2.1
                                        have p294_3 := h294c.2.2.2
                                        linarith only [hlam, p294_0]
                                    · linarith only [h2, h276, h288, h293, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                                  · linarith only [h2, h276, h279, h292, hlam]
                            · linarith only [h2, h276, h287, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
                  · linarith only [h0, h260, h339, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
                    · linarith only [h0, h258, h341, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h343 | h343
                      · linarith only [h1, h258, h339, h343, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
                        · linarith only [h1, h258, h345, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h347 | h347
                          · linarith only [h1, h258, h347, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h349 | h349
                            · linarith only [h1, h2, h276, h339, h349, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                            · linarith only [h1, h2, h339, h349, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h352 | h352
      · linarith only [h1, h352, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h354 | h354
        · linarith only [h1, h354, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h356 | h356
          · linarith only [h0, h1, h356, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h358 | h358
            · linarith only [h0, h1, h358, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h360 | h360
              · linarith only [h0, h1, h360, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h362 | h362
                · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
                  · linarith only [h0, h1, h356, h363, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                    · linarith only [h358, h362, h365, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h367 | h367
                      · linarith only [h0, h354, h360, h367, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h369 | h369
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h370 | h370
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h371 | h371
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h372 | h372
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h373 | h373
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h374 | h374
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h375 | h375
                                    · linarith only [h369, h375, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
                                    · linarith only [h352, h362, h369, h375, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi3]
                                  · linarith only [h352, h362, h365, h374, hlam]
                                · linarith only [h363, h370, h373, hlam]
                              · linarith only [h0, h354, h363, h369, h371, h372, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h352, h362, h371, hlam]
                          · linarith only [h0, h1, h370, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h369, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                  · linarith only [h0, h1, h384, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h386 | h386
                    · linarith only [h0, h1, h386, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h388 | h388
                      · linarith only [h0, h1, h388, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                            · linarith only [h0, h352, h362, h390, h392, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · linarith only [h0, h352, h392, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h391, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h390, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h397 | h397
    · rcases m.htr 0 1 4 (by decide) (by decide) with h398 | h398
      · linarith only [h0, h398, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h400 | h400
        · linarith only [h0, h400, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h402 | h402
          · rcases m.htr 0 2 4 (by decide) (by decide) with h403 | h403
            · rcases m.htr 0 2 5 (by decide) (by decide) with h404 | h404
              · rcases m.htr 0 4 5 (by decide) (by decide) with h405 | h405
                · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h408 | h408
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h409 | h409
                        · linarith only [h397, h398, h407, h409, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
                          · linarith only [h397, h398, h407, h411, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h413 | h413
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h414 | h414
                              · linarith only [h397, h400, h406, h409, h413, h414, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
                                · linarith only [h397, h400, h406, h411, h416, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h418 | h418
                                  · linarith only [h0, h403, h418, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                                  · linarith only [h398, h405, h407, h418, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                            · linarith only [h398, h405, h413, hlam]
                      · linarith only [h0, h404, h408, hlam]
                    · linarith only [h0, h403, h407, hlam]
                  · linarith only [h0, h402, h406, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h426 | h426
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h427 | h427
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h428 | h428
                        · linarith only [h397, h400, h428, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h430 | h430
                          · linarith only [h397, h398, h426, h430, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h432 | h432
                            · linarith only [h397, h398, h405, h425, h426, h432, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · linarith only [h397, h398, h425, h432, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h397, h400, h404, h425, h427, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h0, h403, h426, hlam]
                  · linarith only [h0, h397, h402, h425, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h438 | h438
                · linarith only [h403, h404, h438, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h440 | h440
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h441 | h441
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h442 | h442
                      · linarith only [h0, h397, h404, h440, h442, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                        · linarith only [h397, h444, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h446 | h446
                          · linarith only [h397, h398, h441, h442, h446, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h448 | h448
                            · linarith only [h438, h441, h442, h448, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · linarith only [h397, h398, h448, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h397, h403, h440, h441, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h402, h440, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h453 | h453
              · rcases m.htr 0 4 5 (by decide) (by decide) with h454 | h454
                · rcases m.htr 1 2 3 (by decide) (by decide) with h455 | h455
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h456 | h456
                    · linarith only [h403, h453, h456, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h458 | h458
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
                        · linarith only [h397, h400, h456, h458, h459, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h461 | h461
                          · linarith only [h397, h400, h456, h458, h461, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h463 | h463
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                              · linarith only [h397, h400, h455, h456, h458, h459, h464, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                              · linarith only [h397, h400, h456, h458, h464, hc13, hc34, hlam, hphi]
                            · linarith only [h397, h400, h454, h455, h456, h458, h463, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h453, h458, hlam]
                  · linarith only [h0, h397, h402, h455, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h403, h453, h454, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h471 | h471
                · rcases m.htr 1 2 3 (by decide) (by decide) with h472 | h472
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h473 | h473
                    · linarith only [h0, h397, h403, h472, h473, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h475 | h475
                      · linarith only [h0, h397, h453, h472, h473, h475, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h477 | h477
                        · linarith only [h397, h477, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h479 | h479
                          · linarith only [h0, h397, h473, h479, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h481 | h481
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h482 | h482
                              · linarith only [h0, h397, h472, h475, h477, h481, h482, hlam]
                              · linarith only [h0, h397, h472, h473, h482, hc23, hc34, hlam, hphi]
                            · linarith only [h397, h398, h472, h481, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h397, h402, h472, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h487 | h487
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h488 | h488
                    · linarith only [h0, h397, h403, h487, h488, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h490 | h490
                      · linarith only [h0, h397, h453, h487, h488, h490, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h492 | h492
                        · linarith only [h397, h492, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h494 | h494
                          · linarith only [h0, h397, h488, h494, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h496 | h496
                            · linarith only [h471, h496, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                            · linarith only [h397, h398, h487, h496, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h397, h402, h403, h487, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h397, h402, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h501 | h501
      · linarith only [h397, h501, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h503 | h503
        · linarith only [h397, h503, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h505 | h505
          · rcases m.htr 0 2 4 (by decide) (by decide) with h506 | h506
            · rcases m.htr 0 2 5 (by decide) (by decide) with h507 | h507
              · rcases m.htr 0 4 5 (by decide) (by decide) with h508 | h508
                · rcases m.htr 1 2 3 (by decide) (by decide) with h509 | h509
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h510 | h510
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h511 | h511
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h512 | h512
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h513 | h513
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h514 | h514
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h515 | h515
                              · linarith only [h0, h505, h515, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h517 | h517
                                · linarith only [h509, h512, h515, h517, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h519 | h519
                                  · linarith only [h0, h506, h519, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                                  · linarith only [h501, h508, h509, h512, h519, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                            · linarith only [h501, h508, h514, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h523 | h523
                            · linarith only [h512, h513, h523, hlam]
                            · linarith only [h501, h508, h523, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h526 | h526
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h527 | h527
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h528 | h528
                              · linarith only [h512, h526, h528, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h530 | h530
                                · linarith only [h0, h506, h528, h530, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                                · linarith only [h512, h526, h530, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h503, h506, h508, h512, h526, h527, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h534 | h534
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h535 | h535
                              · linarith only [h397, h512, h535, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h537 | h537
                                · linarith only [h0, h397, h506, h526, h535, h537, hc01, hlam, hphi, u1elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h539 | h539
                                  · linarith only [h0, h506, h539, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                                  · linarith only [h0, h506, h508, h539, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                            · linarith only [h501, h503, h508, h534, hc01, hlam, hphi, u1elo4]
                      · linarith only [h0, h507, h511, hlam]
                    · linarith only [h0, h506, h510, hlam]
                  · linarith only [h0, h505, h509, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h546 | h546
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h547 | h547
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h548 | h548
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h549 | h549
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h551 | h551
                            · linarith only [h508, h546, h549, h551, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                              · linarith only [h0, h505, h553, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h555 | h555
                                · linarith only [h546, h549, h553, h555, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h557 | h557
                                  · linarith only [h501, h551, h557, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h559 | h559
                                    · linarith only [h501, h546, h549, h551, h559, hc01, hlam, hphi, u1elo1]
                                    · rcases h2bigk with h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        rcases p561_3 (m.d 0 2) (by simp) with h564 | h564
                                        · rcases p561_3 (m.d 1 2) (by simp) with h565 | h565
                                          · rcases p561_3 (m.d 2 3) (by simp) with h566 | h566
                                            · linarith only [h566, hlam, p561_0]
                                            · rcases p561_3 (m.d 2 4) (by simp) with h568 | h568
                                              · linarith only [h506, h568, hlam]
                                              · linarith only [h553, h568, hlam]
                                          · linarith only [h546, h565, hlam]
                                        · linarith only [h564, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, p561_1, u1elo1, u4ehi2]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p561_1, u1elo1, u5ehi2]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, p561_1, u1elo1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        rcases p561_3 (m.d 0 2) (by simp) with h577 | h577
                                        · linarith only [h0, h577, hlam]
                                        · linarith only [h505, h577, hlam]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p561_1, u1elo1, u4ehi2]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h557, hlam, hphi, ht01, ht0b, ht45, ht5b, p561_1, u1elo1, u4ehi2]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h505, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h546, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h553, hlam, p561_1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h555, hlam, p561_1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h506, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h547, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, h507, h557, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p561_1, u1elo1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h557, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h507, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h548, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h546, h550, h555, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p561_1, u1elo1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h546, h550, h555, hlam, hphi, ht01, ht0b, ht45, ht5b, p561_1, u1elo1, u4ehi2]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, p561_0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
                            · linarith only [h508, h597, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h599 | h599
                              · linarith only [h0, h505, h599, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                              · linarith only [h549, h550, h599, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h602 | h602
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h603 | h603
                            · linarith only [h506, h508, h603, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                            · linarith only [h549, h602, h603, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h606 | h606
                            · linarith only [h506, h508, h606, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h608 | h608
                              · linarith only [h0, h505, h608, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h610 | h610
                                · linarith only [h397, h602, h610, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h612 | h612
                                  · linarith only [h0, h501, h506, h606, h612, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h614 | h614
                                    · linarith only [h397, h549, h606, h614, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h397, h549, h614, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h507, h548, hlam]
                    · linarith only [h0, h501, h506, h507, h547, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
                  · linarith only [h0, h505, h546, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h620 | h620
                · linarith only [h506, h507, h620, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h623 | h623
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h624 | h624
                      · linarith only [h505, h507, h624, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h626 | h626
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h627 | h627
                          · linarith only [h622, h624, h627, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h629 | h629
                            · linarith only [h620, h626, h627, h629, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h631 | h631
                              · linarith only [h0, h505, h631, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                              · linarith only [h626, h627, h631, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h634 | h634
                          · linarith only [h623, h624, h626, h634, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h636 | h636
                            · linarith only [h506, h620, h623, h636, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h638 | h638
                              · linarith only [h397, h626, h638, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h640 | h640
                                · linarith only [h397, h634, h640, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h642 | h642
                                  · linarith only [h0, h501, h506, h624, h636, h640, h642, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                                  · linarith only [h0, h506, h624, h642, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h0, h506, h623, hlam]
                  · linarith only [h0, h505, h622, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h647 | h647
              · rcases m.htr 0 4 5 (by decide) (by decide) with h648 | h648
                · rcases m.htr 1 2 3 (by decide) (by decide) with h649 | h649
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h650 | h650
                    · linarith only [h506, h647, h650, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h652 | h652
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h653 | h653
                        · linarith only [h649, h650, h653, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h655 | h655
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h656 | h656
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h657 | h657
                              · linarith only [h653, h655, h657, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h659 | h659
                                · linarith only [h0, h505, h650, h657, h659, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                · linarith only [h649, h650, h655, h657, h659, hc23, hc34, hlam, hphi]
                            · linarith only [h503, h648, h649, h650, h655, h656, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h663 | h663
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h664 | h664
                              · linarith only [h0, h505, h664, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h666 | h666
                                · linarith only [h0, h397, h505, h650, h655, h664, h666, hc03, hc34, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h668 | h668
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h669 | h669
                                    · rcases h2bigk with h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h0, hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h0, h650, h664, hc23, hc34, hlam, hphi, p670_1]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h506, hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h0, h650, h664, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p670_1, u5ehi2]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h650, h664, hc02, hc34, hlam, hphi, ht23, p670_1]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h650, h664, hc23, hc34, hlam, hphi, p670_1]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h650, hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h650, h664, h668, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p670_1, u4ehi4]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h505, hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h649, hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h664, hlam, p670_1]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h666, hlam, p670_1]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h647, h664, h668, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p670_1, u4ehi4]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h0, h664, hc01, hc34, hlam, hphi, ht12, ht23, p670_1]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        rcases p670_3 (m.d 0 2) (by simp) with h688 | h688
                                        · linarith only [h506, h688, hlam]
                                        · linarith only [h505, h688, hlam]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        rcases p670_3 (m.d 0 2) (by simp) with h692 | h692
                                        · linarith only [h506, h692, hlam]
                                        · linarith only [h647, h692, hlam]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h647, hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h652, hlam, p670_0]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h0, h647, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p670_1, u1elo1]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [h668, hlam, p670_1]
                                      · have p670_0 := h670c.1
                                        have p670_1 := h670c.2.1
                                        have p670_2 := h670c.2.2.1
                                        have p670_3 := h670c.2.2.2
                                        linarith only [hlam, p670_0]
                                    · linarith only [h0, h647, h650, h664, h668, h669, hlam]
                                  · linarith only [h0, h647, h650, h668, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                            · linarith only [h501, h648, h663, hlam]
                      · linarith only [h0, h647, h652, hlam]
                  · linarith only [h0, h505, h649, hlam]
                · linarith only [h506, h647, h648, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h706 | h706
                · rcases m.htr 1 2 3 (by decide) (by decide) with h707 | h707
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h708 | h708
                    · linarith only [h0, h506, h708, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h710 | h710
                      · linarith only [h505, h647, h708, h710, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h712 | h712
                        · linarith only [h707, h708, h712, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h714 | h714
                          · linarith only [h707, h710, h714, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h716 | h716
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h717 | h717
                              · linarith only [h0, h505, h717, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h719 | h719
                                · linarith only [h0, h505, h708, h714, h717, h719, hc13, hc34, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h721 | h721
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h722 | h722
                                    · rcases h2bigk with h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h0, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h0, h710, h717, h721, hc23, hc34, hlam, hphi, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h506, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h647, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h710, h717, h721, hc02, hc34, hlam, hphi, ht23, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h710, h717, h721, hc23, hc34, hlam, hphi, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h708, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h710, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h505, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h707, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h717, hlam, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h719, hlam, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h505, h717, hc23, hc34, hlam, hphi, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h0, h717, hc01, hc34, hlam, hphi, ht12, ht23, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        rcases p723_3 (m.d 0 2) (by simp) with h741 | h741
                                        · linarith only [h506, h741, hlam]
                                        · linarith only [h505, h741, hlam]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h505, h647, h717, hc23, hc34, hlam, hphi, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h505, h719, hc23, hc35, hlam, hphi, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h397, h707, h719, hc01, hc35, hlam, hphi, ht12, ht23, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        rcases p723_3 (m.d 0 2) (by simp) with h748 | h748
                                        · linarith only [h647, h748, hlam]
                                        · linarith only [h505, h748, hlam]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h721, hlam, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [hlam, p723_0]
                                    · linarith only [h505, h506, h717, h722, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h397, h501, h706, h707, h708, h721, hc01, hlam, hphi, u1elo3]
                            · linarith only [h501, h706, h716, hlam]
                  · linarith only [h0, h505, h707, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h757 | h757
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h758 | h758
                    · linarith only [h505, h506, h758, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h760 | h760
                      · linarith only [h505, h647, h758, h760, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h762 | h762
                        · linarith only [h757, h758, h762, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h764 | h764
                          · linarith only [h757, h760, h764, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h766 | h766
                            · linarith only [h706, h766, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h768 | h768
                              · linarith only [h0, h505, h758, h762, h766, h768, hc13, hc45, hlam, hphi, ht34]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h770 | h770
                                · linarith only [h0, h397, h505, h758, h764, h766, h770, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h772 | h772
                                  · linarith only [h0, h505, h758, h766, h768, h772, hc23, hc34, hlam, hphi]
                                  · linarith only [h505, h506, h772, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h505, h506, h757, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h776 | h776
            · rcases m.htr 0 2 5 (by decide) (by decide) with h777 | h777
              · rcases m.htr 0 4 5 (by decide) (by decide) with h778 | h778
                · rcases m.htr 1 2 3 (by decide) (by decide) with h779 | h779
                  · linarith only [h505, h776, h778, h779, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h781 | h781
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h782 | h782
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h784 | h784
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h785 | h785
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h786 | h786
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h787 | h787
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h788 | h788
                                  · linarith only [h0, h776, h779, h788, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                  · linarith only [h501, h778, h779, h781, h788, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                                · linarith only [h503, h779, h781, h785, h787, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h503, h779, h781, h785, h786, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h501, h778, h785, hlam]
                          · linarith only [h779, h782, h784, hlam]
                        · linarith only [h779, h781, h783, hlam]
                      · linarith only [h0, h777, h782, hlam]
                    · linarith only [h0, h776, h781, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h798 | h798
                  · linarith only [h505, h776, h798, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h800 | h800
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h801 | h801
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h802 | h802
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h803 | h803
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h804 | h804
                            · linarith only [h776, h778, h804, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h806 | h806
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h807 | h807
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h808 | h808
                                  · linarith only [h0, h776, h798, h804, h808, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h810 | h810
                                    · linarith only [h501, h804, h806, h810, hc01, hc24, hlam, hphi, ht12]
                                    · rcases h2bigk with h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h0, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h505, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h0, h798, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p812_1, u4ehi2]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h0, h798, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p812_1, u5ehi2]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h798, hc02, hc23, hlam, hphi, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h798, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h798, h806, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p812_1, u4ehi3]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h798, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p812_1, u5ehi2]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h776, h806, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p812_1, u4ehi3]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        rcases p812_3 (m.d 0 2) (by simp) with h826 | h826
                                        · linarith only [h505, h826, hlam]
                                        · linarith only [h776, h826, hlam]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        rcases p812_3 (m.d 0 2) (by simp) with h829 | h829
                                        · linarith only [h505, h829, hlam]
                                        · linarith only [h777, h829, hlam]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h776, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h800, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h806, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h808, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h777, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h801, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h807, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h777, h806, hc02, hlam, hphi, ht0b, ht45, ht5b, p812_1, u4ehi3]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [hlam, p812_0]
                                · linarith only [h0, h798, h807, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h798, h806, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h798, h801, h803, hlam]
                        · linarith only [h798, h800, h802, hlam]
                      · linarith only [h0, h777, h801, hlam]
                    · linarith only [h0, h776, h800, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h848 | h848
                · linarith only [h776, h777, h848, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h850 | h850
                  · linarith only [h0, h505, h850, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h852 | h852
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h853 | h853
                      · linarith only [h776, h777, h853, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h855 | h855
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h856 | h856
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h857 | h857
                            · linarith only [h848, h857, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h859 | h859
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h860 | h860
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h861 | h861
                                  · linarith only [h776, h857, h861, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                  · linarith only [h0, h776, h853, h861, hc45, hlam, hphi, u4ehi2]
                                · linarith only [h505, h776, h856, h859, h860, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi3]
                              · linarith only [h0, h776, h850, h859, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h866 | h866
                            · linarith only [h776, h848, h866, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h868 | h868
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h869 | h869
                                · linarith only [h397, h856, h869, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h505, h776, h868, h869, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                              · linarith only [h0, h776, h850, h868, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · linarith only [h850, h852, h855, hlam]
                    · linarith only [h0, h776, h852, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h875 | h875
              · rcases m.htr 0 4 5 (by decide) (by decide) with h876 | h876
                · rcases m.htr 1 2 3 (by decide) (by decide) with h877 | h877
                  · linarith only [h505, h875, h877, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h879 | h879
                    · linarith only [h776, h875, h877, h879, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h881 | h881
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h882 | h882
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h883 | h883
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h884 | h884
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h885 | h885
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h886 | h886
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h887 | h887
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h888 | h888
                                    · linarith only [h882, h888, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
                                    · linarith only [h0, h875, h879, h882, h887, h888, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi3]
                                  · linarith only [h0, h501, h876, h879, h882, h887, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                                · linarith only [h505, h875, h886, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h0, h875, h877, h885, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h501, h876, h884, hlam]
                          · linarith only [h877, h881, h883, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h896 | h896
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h897 | h897
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h898 | h898
                              · linarith only [h882, h896, h898, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · linarith only [h505, h875, h898, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h501, h876, h897, hlam]
                          · linarith only [h877, h881, h896, hlam]
                      · linarith only [h0, h875, h881, hlam]
                · linarith only [h776, h875, h876, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h905 | h905
                · rcases m.htr 1 2 3 (by decide) (by decide) with h906 | h906
                  · linarith only [h0, h505, h906, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h908 | h908
                    · linarith only [h776, h905, h908, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h910 | h910
                      · linarith only [h0, h875, h910, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h912 | h912
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h913 | h913
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h914 | h914
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h915 | h915
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h916 | h916
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h917 | h917
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h918 | h918
                                    · linarith only [h912, h918, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
                                    · linarith only [h501, h905, h912, h918, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi3]
                                  · linarith only [h501, h905, h912, h917, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
                                · linarith only [h0, h505, h913, h916, hc01, hlam, hphi, u1elo2]
                              · linarith only [h0, h906, h915, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h501, h905, h914, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h925 | h925
                            · linarith only [h912, h913, h925, hlam]
                            · linarith only [h501, h905, h925, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h928 | h928
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h929 | h929
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h930 | h930
                              · linarith only [h912, h928, h930, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · linarith only [h0, h906, h930, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h501, h905, h929, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h934 | h934
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h935 | h935
                              · linarith only [h397, h912, h935, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h906, h935, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h501, h905, h934, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
                  · linarith only [h0, h505, h939, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h941 | h941
                    · linarith only [h0, h776, h941, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h943 | h943
                      · linarith only [h0, h875, h939, h943, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h945 | h945
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h946 | h946
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h947 | h947
                            · linarith only [h905, h945, h947, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h949 | h949
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h950 | h950
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h951 | h951
                                  · linarith only [h0, h941, h947, h951, hc01, hc24, hlam, hphi, ht12]
                                  · linarith only [h0, h941, h951, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h0, h505, h946, h950, hc01, hlam, hphi, u1elo2]
                              · linarith only [h0, h939, h945, h949, hc01, hlam, hphi, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h956 | h956
                            · linarith only [h905, h956, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h958 | h958
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h959 | h959
                                · linarith only [h945, h946, h959, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                · linarith only [h0, h939, h959, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h939, h945, h958, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h963 | h963
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h964 | h964
                            · linarith only [h905, h964, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                            · linarith only [h945, h963, h964, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h967 | h967
                            · linarith only [h905, h967, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h969 | h969
                              · linarith only [h397, h945, h969, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h939, h969, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
