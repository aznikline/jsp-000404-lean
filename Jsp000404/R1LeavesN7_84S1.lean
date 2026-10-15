import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_0_L_R_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
              · linarith only [h0, h3, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h9, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
              · linarith only [h0, h3, h9, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h13 | h13
          · linarith only [h13, h3, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
            · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
              · linarith only [h16, h3, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h13, h18, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
                  · linarith only [h0, h20, h3, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                      · linarith only [h1, h23, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                      · linarith only [h1, h15, h18, h23, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                      · linarith only [h1, h26, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                      · linarith only [h1, h15, h18, h26, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
              · linarith only [h0, h29, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
                · linarith only [h0, h31, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                  · linarith only [h1, h31, h33, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                      · linarith only [h1, h13, h15, h36, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h39 | h39
                          · linarith only [h0, h13, h15, h38, h39, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h13, h39, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h35, h38, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
                      · linarith only [h1, h43, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                        · linarith only [h29, h35, h45, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h3, h45, hc34, hlam, hphi, ht23, u2ehi1]
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4, u2ehi1]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h50 | h50
    · rcases m.htr 0 1 5 (by decide) (by decide) with h51 | h51
      · linarith only [h0, h51, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h53 | h53
        · rcases m.htr 0 2 4 (by decide) (by decide) with h54 | h54
          · rcases m.htr 0 4 5 (by decide) (by decide) with h55 | h55
            · linarith only [h0, h50, h55, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
              · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                · linarith only [h0, h50, h58, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi3]
                · linarith only [h0, h53, h58, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h53, h57, hlam]
          · linarith only [h53, h54, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h63 | h63
          · linarith only [h53, h63, hc23, hlam, hphi, u2ehi3]
          · linarith only [h0, h50, h63, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h66 | h66
      · linarith only [h0, h66, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h68 | h68
        · rcases m.htr 0 2 4 (by decide) (by decide) with h69 | h69
          · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
            · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
              · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
                · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h74 | h74
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
                          · linarith only [h0, h68, h76, h77, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                          · linarith only [h50, h70, h71, h74, h77, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi3]
                        · linarith only [h71, h74, h76, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                      · linarith only [h50, h70, h75, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                        · linarith only [h0, h68, h74, h83, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                          · linarith only [h0, h69, h85, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                          · linarith only [h50, h70, h83, h85, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi2]
                      · linarith only [h0, h50, h69, h70, h82, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h68, h73, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h68, h72, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h68, h71, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
              · rcases m.htr 1 2 4 (by decide) (by decide) with h93 | h93
                · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                      · linarith only [h69, h70, h95, h96, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
                          · linarith only [h50, h68, h96, h98, h99, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
                            · linarith only [h0, h101, h50, h68, h96, h98, hc01, hlam, hphi, u1elo1]
                            · rcases h4bigk with h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h50, hlam, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h50, h96, hc24, hc45, hlam, hphi, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h50, h96, hc34, hc45, hlam, hphi, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h70, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h96, hc04, hc45, hlam, hphi, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h96, hc45, hlam, hphi, ht23, ht34, p103_1, u2ehi3]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h96, hc34, hc45, hlam, hphi, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h96, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h69, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h93, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h50, h69, h96, hc34, hc45, hlam, hphi, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h99, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h69, hc34, hlam, hphi, ht23, p103_1, u2ehi3]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h95, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h98, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h101, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h69, hc45, hlam, hphi, ht23, ht34, p103_1, u2ehi3]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h0, h50, h68, h98, hc01, hc45, hlam, hphi, ht23, ht34, p103_1, u1elo1, u2ehi3]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hc45, hlam, hphi, ht23, ht34, p103_1, u2ehi3]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                rcases p103_3 (m.d 0 4) (by simp) with h127 | h127
                                · linarith only [h127, h70, hlam]
                                · linarith only [h0, h127, h68, h69, h98, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi3]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                        · linarith only [h92, h95, h98, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                      · linarith only [h132, h69, h70, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                        · linarith only [h0, h134, h68, h95, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h136 | h136
                          · linarith only [h132, h136, h50, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
                            · linarith only [h132, h138, h50, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h138, h92, h95, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h69, h94, hc25, hlam, hphi, u2ehi3]
                · linarith only [h0, h69, h93, hlam]
              · linarith only [h0, h69, h92, hc23, hlam, hphi, u2ehi3]
          · linarith only [h68, h69, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h145 | h145
          · linarith only [h145, h68, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h147 | h147
            · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
              · linarith only [h148, h68, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h150 | h150
                · linarith only [h145, h150, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
                  · linarith only [h148, h152, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                            · linarith only [h154, h158, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                            · rcases h4bigk with h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h50, hlam, p160_1]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h145, hlam, p160_1]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                rcases p160_3 (m.d 0 4) (by simp) with h164 | h164
                                · rcases p160_3 (m.d 1 4) (by simp) with h165 | h165
                                  · rcases p160_3 (m.d 2 4) (by simp) with h166 | h166
                                    · rcases p160_3 (m.d 3 4) (by simp) with h167 | h167
                                      · linarith only [h167, hlam, p160_0]
                                      · rcases p160_3 (m.d 4 5) (by simp) with h169 | h169
                                        · linarith only [h147, h169, hlam]
                                        · linarith only [h158, h169, hlam]
                                    · linarith only [h156, h166, hlam]
                                  · linarith only [h154, h165, hlam]
                                · linarith only [h164, hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h158, h50, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p160_1, u1elo3]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h147, hlam, hphi, ht01, ht0b, ht5b, p160_1, u1elo3, u5ehi0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h150, hlam, p160_1]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                rcases p160_3 (m.d 0 4) (by simp) with h179 | h179
                                · linarith only [h179, h50, hlam]
                                · linarith only [h147, h158, h179, hlam]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h154, h158, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p160_1, u1elo2]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h147, h156, h158, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p160_1]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h156, h50, hc01, hc23, hlam, hphi, ht12, p160_1]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                rcases p160_3 (m.d 0 4) (by simp) with h186 | h186
                                · linarith only [h145, h186, hlam]
                                · linarith only [h147, h158, h186, hlam]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                rcases p160_3 (m.d 0 4) (by simp) with h189 | h189
                                · linarith only [h145, h189, hlam]
                                · linarith only [h147, h189, hlam]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h147, h158, hlam, p160_1]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h154, hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h156, hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h158, hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h147, hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h155, hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h157, hlam, p160_0]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [h147, h154, h50, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p160_1, u1elo2]
                              · have p160_0 := h160c.1
                                have p160_1 := h160c.2.1
                                have p160_2 := h160c.2.2.1
                                have p160_3 := h160c.2.2.2
                                linarith only [hlam, p160_0]
                          · linarith only [h147, h154, h157, h50, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi3]
                        · linarith only [h156, h68, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h147, h155, h50, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                        · linarith only [h0, h148, h154, h206, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h206, h68, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h147, h205, h50, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
              · linarith only [h210, h68, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h212 | h212
                · linarith only [h210, h212, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h214 | h214
                  · linarith only [h210, h214, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h216 | h216
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h217 | h217
                      · linarith only [h147, h216, h217, h50, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h220 | h220
                          · linarith only [h212, h217, h220, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h145, h220, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h216, h219, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h224 | h224
                      · linarith only [h145, h147, h224, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                        · linarith only [h0, h210, h216, h226, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h226, h68, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_11_12_14_25_L_0_L_R_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc13 := m.hcor 1 3 (by decide)
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
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
              · linarith only [h0, h2, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h9, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
              · linarith only [h0, h2, h9, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
              · linarith only [h0, h13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
              · linarith only [h0, h13, h2, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
              · linarith only [h0, h16, h2, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h20 | h20
        · linarith only [h2, h20, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h22 | h22
          · rcases m.htr 0 4 5 (by decide) (by decide) with h23 | h23
            · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
              · linarith only [h2, h24, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                · linarith only [h0, h20, h26, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                  · linarith only [h1, h28, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                  · linarith only [h1, h22, h24, h28, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
              · linarith only [h0, h2, h20, h22, h31, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                · linarith only [h1, h31, h33, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                  · linarith only [h1, h35, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                  · linarith only [h1, h22, h31, h35, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
            · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
              · linarith only [h2, h39, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                · linarith only [h0, h20, h41, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                  · linarith only [h1, h22, h43, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                    · linarith only [h1, h45, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                        · linarith only [h0, h2, h22, h48, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h2, h48, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h22, h38, h41, h47, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
              · linarith only [h0, h2, h52, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                · linarith only [h0, h20, h54, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h0, h1, h2, h22, h56, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h1, h58, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                      · linarith only [h38, h60, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                        · linarith only [h2, h22, h62, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h0, h2, h62, hc34, hlam, hphi, ht23, u2ehi1]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h66 | h66
    · rcases m.htr 0 2 3 (by decide) (by decide) with h67 | h67
      · rcases m.htr 0 2 4 (by decide) (by decide) with h68 | h68
        · rcases m.htr 0 3 4 (by decide) (by decide) with h69 | h69
          · linarith only [h0, h66, h69, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
              · linarith only [h0, h66, h72, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
              · linarith only [h0, h66, h67, h72, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
              · linarith only [h0, h66, h75, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
              · linarith only [h0, h67, h69, h75, hc01, hc34, hlam, hphi, ht12, ht23]
        · linarith only [h67, h68, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h66, h67, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h80 | h80
      · rcases m.htr 0 2 4 (by decide) (by decide) with h81 | h81
        · rcases m.htr 0 3 4 (by decide) (by decide) with h82 | h82
          · rcases m.htr 0 4 5 (by decide) (by decide) with h83 | h83
            · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
              · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h87 | h87
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h88 | h88
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                        · linarith only [h0, h80, h89, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                        · linarith only [h66, h82, h89, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi2]
                      · linarith only [h0, h81, h83, h88, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                      · linarith only [h86, h87, h93, hlam]
                      · linarith only [h0, h66, h80, h82, h83, h87, h93, hc35, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, u1elo1, u2ehi2, u4ehi1]
                  · linarith only [h66, h82, h86, hlam]
                · linarith only [h0, h81, h85, hlam]
              · linarith only [h0, h80, h84, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
              · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
                · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                      · linarith only [h103, h83, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                        · linarith only [h0, h105, h80, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                        · linarith only [h105, h66, h82, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                      · linarith only [h102, h108, h66, h81, h82, h83, hc35, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, u1elo3, u2ehi3, u4ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                        · linarith only [h0, h110, h80, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                        · linarith only [h102, h110, h66, h82, hc23, hc35, hlam, hphi]
                  · linarith only [h101, h66, h82, hlam]
                · linarith only [h0, h100, h80, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h80, h99, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h116 | h116
            · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
              · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
                · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                  · linarith only [h117, h119, h66, h82, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                        · linarith only [h119, h121, h123, h80, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                          · linarith only [h0, h123, h125, h81, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                          · linarith only [h121, h125, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi2]
                      · linarith only [h0, h116, h122, h81, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h129 | h129
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                        · linarith only [h0, h130, h80, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                          · linarith only [h0, h121, h132, h66, h81, hc01, hc23, hlam, hphi, u1elo1, u2ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                            · linarith only [h0, h134, h81, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                            · linarith only [h129, h130, h134, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi2]
                      · linarith only [h0, h116, h129, h81, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h0, h118, h80, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h117, h80, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
              · rcases m.htr 1 2 4 (by decide) (by decide) with h141 | h141
                · rcases m.htr 1 3 4 (by decide) (by decide) with h142 | h142
                  · linarith only [h142, h66, h82, hc01, hlam, hphi, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h144 | h144
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                      · linarith only [h116, h145, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                      · linarith only [h142, h144, h145, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h148 | h148
                      · linarith only [h116, h148, h80, h82, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                        · linarith only [h0, h150, h80, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h152 | h152
                          · linarith only [h144, h152, h66, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                            · linarith only [h0, h116, h154, h81, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                              · linarith only [h0, h142, h148, h150, h156, h66, h81, hc01, hc34, hlam, hphi, ht23, u1elo1, u2ehi2]
                              · linarith only [h156, h80, h82, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h141, h81, hlam]
              · linarith only [h0, h140, h80, h82, hc34, hlam, hphi, ht23, u2ehi0]
        · linarith only [h80, h81, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h162 | h162
        · linarith only [h162, h80, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h164 | h164
          · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
            · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
              · linarith only [h166, h80, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
                · linarith only [h162, h165, h166, h168, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h175 | h175
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h176 | h176
                              · linarith only [h164, h176, h66, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                              · linarith only [h164, h165, h176, h66, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi3]
                            · linarith only [h164, h165, h168, h175, h66, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi1]
                          · linarith only [h171, h174, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi2]
                        · linarith only [h0, h166, h173, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h164, h165, h172, h66, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                      · linarith only [h170, h171, h183, hlam]
                      · linarith only [h164, h165, h171, h183, h66, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                  · linarith only [h164, h170, h66, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
              · linarith only [h187, h80, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h189 | h189
                · linarith only [h187, h189, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h193 | h193
                      · linarith only [h165, h193, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h196 | h196
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h197 | h197
                            · linarith only [h189, h193, h197, hc24, hlam, hphi, u2ehi1]
                            · linarith only [h162, h197, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h192, h196, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi2]
                        · linarith only [h0, h187, h195, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                      · linarith only [h165, h202, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                          · linarith only [h164, h192, h205, h66, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h205, h80, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h164, h187, h204, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h164, h191, h66, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h210 | h210
            · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
              · linarith only [h211, h80, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
                · linarith only [h211, h213, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                  · linarith only [h164, h215, h66, hc01, hlam, hphi, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h217 | h217
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h218 | h218
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                        · linarith only [h211, h215, h219, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h219, h80, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h210, h215, h217, h218, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h223 | h223
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                        · linarith only [h164, h224, h80, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h224, h80, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h0, h164, h210, h213, h223, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h228 | h228
              · linarith only [h228, h80, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h230 | h230
                · linarith only [h228, h230, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                  · linarith only [h164, h232, h80, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h234 | h234
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h235 | h235
                      · linarith only [h210, h235, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                      · linarith only [h232, h234, h235, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                      · linarith only [h210, h238, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                        · linarith only [h164, h240, h80, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h240, h80, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_11_12_14_25_L_I_L_0_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                            · linarith only [h1, h12, h14, h4, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                              · linarith only [h1, h12, h16, h4, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                              · linarith only [h16, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h11, hlam, hphi, ht45, u4ehi1, u5elo4]
                      · linarith only [h10, h9, hlam, hphi, ht45, u4ehi3, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                          · linarith only [h21, h23, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                            · linarith only [h25, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                            · linarith only [h21, h25, h9, hc23, hc34, hlam, hphi]
                        · linarith only [h21, h22, h9, hlam, hphi, u5ehi8, u5elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                          · linarith only [h30, h4, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                            · linarith only [h21, h32, h7, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                              · linarith only [h34, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                              · linarith only [h34, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h29, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h5, h8, hc12, hlam, hphi, u2elo0]
                · linarith only [h4, h7, hc12, hlam, hphi, u2elo0]
              · linarith only [h5, h6, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h41 | h41
              · linarith only [h41, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
              · linarith only [h4, h41, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h44 | h44
            · linarith only [h4, h44, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h46 | h46
              · linarith only [h4, h46, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                · linarith only [h4, h48, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                  · linarith only [h0, h44, h50, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                                · linarith only [h1, h4, h52, h58, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                                · linarith only [h2, h44, h54, h58, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                              · linarith only [h1, h4, h44, h52, h54, h57, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
                            · linarith only [h1, h4, h53, h56, hlam]
                          · linarith only [h1, h4, h52, h55, hlam]
                        · linarith only [h54, hlam, hphi, ht45, u4ehi1, u5elo4]
                      · linarith only [h52, h53, hlam, hphi, ht45, u4ehi3, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h66 | h66
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                          · linarith only [h52, h66, h68, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                                · rcases h1bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [hlam, p73_0]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    rcases p73_3 (m.d 0 1) (by simp) with h75 | h75
                                    · rcases p73_3 (m.d 1 2) (by simp) with h76 | h76
                                      · linarith only [h76, hlam, p73_0]
                                      · rcases p73_3 (m.d 1 3) (by simp) with h78 | h78
                                        · linarith only [h1, h78, hlam]
                                        · linarith only [h48, h78, hlam]
                                    · linarith only [h75, hlam, p73_0]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h66, h72, hc01, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi4]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h52, h66, h72, hc01, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi4]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    rcases p73_3 (m.d 0 1) (by simp) with h84 | h84
                                    · rcases p73_3 (m.d 1 2) (by simp) with h85 | h85
                                      · linarith only [h0, h85, hlam]
                                      · rcases p73_3 (m.d 1 3) (by simp) with h87 | h87
                                        · linarith only [h1, h87, hlam]
                                        · linarith only [h66, h87, hlam]
                                    · linarith only [h84, hlam, p73_0]
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
                                    linarith only [h48, hlam, p73_1]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h50, hlam, p73_1]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p73_1, u2elo0, u5ehi6]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h1, hlam, p73_0]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h1, h4, h68, hc12, hc34, hlam, hphi, ht23, p73_1]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [hlam, p73_0]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h52, hlam, p73_0]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h1, h4, h68, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p73_1, u5ehi6]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h2, hlam, p73_0]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h2, h44, hc12, hlam, hphi, p73_1, u2elo3]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h2, h44, h48, hc12, hlam, hphi, p73_1, u2elo3]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [hlam, p73_0]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h2, h44, h66, h72, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u2elo3, u4ehi4]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h3, hlam, p73_0]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p73_1, u5elo1]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h66, hlam, p73_0]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [h67, hlam, p73_0]
                                  · have p73_0 := h73c.1
                                    have p73_1 := h73c.2.1
                                    have p73_2 := h73c.2.2.1
                                    have p73_3 := h73c.2.2.2
                                    linarith only [hlam, p73_0]
                                · linarith only [h2, h4, h44, h67, h68, h72, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                              · linarith only [h2, h44, h67, h71, hlam]
                            · linarith only [h1, h4, h66, h70, hlam]
                        · linarith only [h67, hlam, hphi, ht45, u4ehi1, u5elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                          · linarith only [h115, h116, h52, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                            · linarith only [h116, h118, h66, hc13, hc34, hlam, hphi]
                            · linarith only [h0, h118, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h115, hlam, hphi, ht45, u4ehi1, u5elo4]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h123 | h123
        · rcases m.htr 0 2 3 (by decide) (by decide) with h124 | h124
          · rcases m.htr 0 2 4 (by decide) (by decide) with h125 | h125
            · linarith only [h0, h125, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h127 | h127
              · linarith only [h125, h127, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
              · linarith only [h124, h127, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h130 | h130
            · linarith only [h124, h130, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h132 | h132
              · linarith only [h124, h132, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
                · linarith only [h124, h134, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                  · linarith only [h0, h123, h124, h130, h136, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi6]
                  · linarith only [h123, h136, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi6]
        · linarith only [h1, h123, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h140 | h140
      · rcases m.htr 0 1 5 (by decide) (by decide) with h141 | h141
        · rcases m.htr 0 2 3 (by decide) (by decide) with h142 | h142
          · linarith only [h0, h1, h142, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h144 | h144
            · linarith only [h142, h144, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h146 | h146
              · linarith only [h142, h146, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
                · linarith only [h0, h146, h148, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h1, h141, h148, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi6]
        · linarith only [h140, h141, hlam, hphi, ht45, u4ehi1, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h152 | h152
        · rcases m.htr 0 2 3 (by decide) (by decide) with h153 | h153
          · linarith only [h0, h1, h153, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h155 | h155
            · linarith only [h153, h155, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h157 | h157
              · linarith only [h153, h157, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h159 | h159
                · linarith only [h0, h157, h159, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h1, h152, h159, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi6]
        · linarith only [h0, h152, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h163 | h163
    · rcases m.htr 0 1 4 (by decide) (by decide) with h164 | h164
      · linarith only [h0, h164, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h166 | h166
        · linarith only [h0, h166, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
        · linarith only [h163, h166, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h169 | h169
      · linarith only [h0, h169, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h171 | h171
        · linarith only [h0, h171, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h173 | h173
          · rcases m.htr 0 2 4 (by decide) (by decide) with h174 | h174
            · rcases m.htr 0 2 5 (by decide) (by decide) with h175 | h175
              · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
                · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h179 | h179
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                          · linarith only [h173, h181, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                            · linarith only [h176, h178, h181, h183, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                              · linarith only [h0, h174, h185, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                              · linarith only [h185, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h180, hlam, hphi, ht45, u4ehi1, u5elo4]
                      · linarith only [h178, h179, hlam, hphi, ht45, u4ehi3, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h190 | h190
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h191 | h191
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h192 | h192
                          · linarith only [h178, h190, h192, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                            · linarith only [h0, h174, h192, h194, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                            · linarith only [h178, h190, h194, hc23, hc34, hlam, hphi]
                        · linarith only [h191, hlam, hphi, ht45, u4ehi1, u5elo4]
                      · linarith only [h163, h190, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h174, h177, hlam]
                · linarith only [h0, h174, h176, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
              · linarith only [h174, h175, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h202 | h202
              · linarith only [h174, h202, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
              · linarith only [h173, h202, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h205 | h205
            · linarith only [h173, h205, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h207 | h207
              · linarith only [h173, h207, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h209 | h209
                · linarith only [h173, h209, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h209, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_11_12_14_25_L_R_L_0_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                        · linarith only [h0, h10, h11, h5, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h14, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                          · linarith only [h16, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                            · linarith only [h0, h10, h16, h18, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · linarith only [h10, h18, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h2, h4, h9, hlam, hphi, ht12, u1ehi3, u2elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h22, h7, h8, hlam]
                    · linarith only [h2, h22, h4, hlam, hphi, ht12, u1ehi3, u2elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                      · linarith only [h25, h27, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                        · linarith only [h2, h27, h29, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                        · linarith only [h25, h29, h7, hc23, hc34, hlam, hphi]
                    · linarith only [h2, h25, h26, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                      · linarith only [h34, h7, hlam, hphi, ht12, u1ehi2, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                        · linarith only [h0, h25, h34, h36, h6, hlam, hphi, ht12, u1ehi2, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                          · linarith only [h0, h38, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h40 | h40
                            · rcases h4bigk with h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h2, h33, h34, h38, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p41_1, u2elo0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                rcases p41_3 (m.d 0 4) (by simp) with h44 | h44
                                · rcases p41_3 (m.d 1 4) (by simp) with h45 | h45
                                  · linarith only [h1, h45, hlam]
                                  · linarith only [h45, h6, hlam]
                                · linarith only [h2, h44, hlam]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h2, h25, h40, hlam, hphi, ht12, p41_1, u1ehi2, u2elo0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h2, h34, h38, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p41_1, u2elo0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h1, hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                rcases p41_3 (m.d 0 4) (by simp) with h53 | h53
                                · rcases p41_3 (m.d 1 4) (by simp) with h54 | h54
                                  · rcases p41_3 (m.d 2 4) (by simp) with h55 | h55
                                    · linarith only [h55, h6, hlam]
                                    · rcases p41_3 (m.d 3 4) (by simp) with h57 | h57
                                      · rcases p41_3 (m.d 4 5) (by simp) with h58 | h58
                                        · linarith only [h33, h58, hlam]
                                        · linarith only [h38, h58, hlam]
                                      · linarith only [h34, h57, hlam]
                                  · linarith only [h54, h6, hlam]
                                · linarith only [h2, h53, hlam]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h7, hlam, p41_1]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h1, h34, h38, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p41_1]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h2, hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h6, hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h34, hlam, p41_1]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h38, hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h1, hc34, hlam, hphi, ht12, ht23, p41_1, u1ehi3]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h2, h34, h38, h4, hc23, hc34, hlam, hphi, ht12, p41_1, u1ehi3, u2elo0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                rcases p41_3 (m.d 0 4) (by simp) with h73 | h73
                                · linarith only [h2, h7, h73, hlam, hphi, ht12, u1ehi2, u2elo0]
                                · linarith only [h2, h73, hlam]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h34, h38, hc23, hc34, hlam, hphi, p41_1]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h4, hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h33, hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h1, h2, h33, h34, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p41_1, u2elo0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [h40, hlam, p41_0]
                              · have p41_0 := h41c.1
                                have p41_1 := h41c.2.1
                                have p41_2 := h41c.2.2.1
                                have p41_3 := h41c.2.2.2
                                linarith only [hlam, p41_0]
                            · linarith only [h1, h2, h33, h40, h7, hlam, hphi, ht12, u1ehi2, u2elo0]
                    · linarith only [h2, h33, h4, hlam, hphi, ht12, u1ehi3, u2elo0]
              · linarith only [h6, hlam, hphi, ht12, u1ehi1, u2elo3]
            · linarith only [h5, hlam, hphi, ht12, u1ehi1, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
            · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                    · linarith only [h1, h4, h91, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                        · linarith only [h87, h94, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                        · linarith only [h0, h87, h90, h93, h94, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                        · linarith only [h2, h93, h97, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
                          · linarith only [h0, h1, h4, h87, h89, h93, h99, hlam, hphi, ht12, u1ehi3, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
                            · linarith only [h0, h1, h101, h4, h87, h89, hlam, hphi, ht12, u1ehi3, u2elo0]
                            · rcases h4bigk with h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h4, hc45, hlam, hphi, ht12, ht23, ht34, p103_1, u1ehi3]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h4, hc24, hc45, hlam, hphi, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h4, h93, hc23, hc45, hlam, hphi, ht34, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h4, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h1, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h1, h4, h93, hc23, hc45, hlam, hphi, ht34, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h1, h4, h93, hc23, hc45, hlam, hphi, ht34, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h91, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h2, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h88, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h93, hlam, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h99, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h0, h101, h87, h90, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p103_1, u2elo0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h89, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h0, h101, h87, h90, h93, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p103_1, u2elo0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h101, hlam, p103_0]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h1, hc45, hlam, hphi, ht12, ht23, ht34, p103_1, u1ehi3]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p103_1, u1ehi3]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                rcases p103_3 (m.d 0 4) (by simp) with h126 | h126
                                · linarith only [h126, h4, hlam]
                                · linarith only [h126, h2, hlam]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [h93, hc23, hc45, hlam, hphi, ht34, p103_1]
                              · have p103_0 := h103c.1
                                have p103_1 := h103c.2.1
                                have p103_2 := h103c.2.2.1
                                have p103_3 := h103c.2.2.2
                                linarith only [hlam, p103_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                    · linarith only [h1, h131, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h134 | h134
                        · linarith only [h0, h134, h87, h90, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h136 | h136
                          · linarith only [h1, h136, h4, hlam, hphi, ht12, u1ehi3, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
                            · linarith only [h0, h1, h133, h138, h4, h87, hlam, hphi, ht12, u1ehi3, u2elo0]
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
                                linarith only [h2, hlam, hphi, ht12, p140_1, u1ehi3, u2elo0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h4, hc24, hc45, hlam, hphi, p140_1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h4, hc34, hc45, hlam, hphi, p140_1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h4, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h1, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h1, h133, h4, hc34, hc45, hlam, hphi, p140_1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h1, h4, hc34, hc45, hlam, hphi, p140_1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h131, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h2, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h88, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p140_1, u2elo0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h136, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h1, hc34, hlam, hphi, ht12, ht23, p140_1, u1ehi3]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h89, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h133, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h138, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h1, hc45, hlam, hphi, ht12, ht23, ht34, p140_1, u1ehi3]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p140_1, u1ehi3]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                rcases p140_3 (m.d 0 4) (by simp) with h163 | h163
                                · linarith only [h163, h4, hlam]
                                · linarith only [h163, h2, hlam]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                rcases p140_3 (m.d 0 4) (by simp) with h166 | h166
                                · linarith only [h166, h4, hlam]
                                · linarith only [h0, h1, h133, h166, h87, hlam, hphi, ht12, u1ehi3, u2elo0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                      · linarith only [h133, h89, h90, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h172 | h172
                    · linarith only [h1, h172, h4, hlam]
                    · linarith only [h171, h172, h89, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                    · linarith only [h1, h175, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                      · linarith only [h177, h89, hlam, hphi, ht12, u1ehi2, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                        · linarith only [h171, h179, hlam, hphi, ht12, u1ehi2, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h181 | h181
                          · linarith only [h0, h181, h4, h88, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h183 | h183
                            · linarith only [h1, h183, h4, h89, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                            · linarith only [h183, h89, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h88, hlam, hphi, ht12, u1ehi1, u2elo3]
            · linarith only [h87, hlam, hphi, ht12, u1ehi1, u2elo2]
        · linarith only [h0, h3, hlam, hphi, ht12, u1ehi1, u2elo4]
      · linarith only [h0, h2, hlam, hphi, ht12, u1ehi1, u2elo3]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · linarith only [h0, hlam, hphi, ht12, u1ehi0, u2elo1]

theorem r1l7_11_12_14_L_I_L_R_L_0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · rcases h1bigk with h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h11, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p14_1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h13, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p14_1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                rcases p14_3 (m.d 0 1) (by simp) with h18 | h18
                                · rcases p14_3 (m.d 1 2) (by simp) with h19 | h19
                                  · rcases p14_3 (m.d 1 3) (by simp) with h20 | h20
                                    · linarith only [h0, h20, hlam]
                                    · linarith only [h20, h8, hlam]
                                  · linarith only [h19, h6, hlam]
                                · linarith only [h18, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                rcases p14_3 (m.d 0 1) (by simp) with h25 | h25
                                · rcases p14_3 (m.d 1 2) (by simp) with h26 | h26
                                  · rcases p14_3 (m.d 1 3) (by simp) with h27 | h27
                                    · linarith only [h0, h27, hlam]
                                    · linarith only [h27, h9, hlam]
                                  · linarith only [h26, h7, hlam]
                                · linarith only [h25, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h0, h13, h8, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14_1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h13, h8, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14_1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                rcases p14_3 (m.d 0 1) (by simp) with h35 | h35
                                · rcases p14_3 (m.d 1 2) (by simp) with h36 | h36
                                  · rcases p14_3 (m.d 1 3) (by simp) with h37 | h37
                                    · linarith only [h37, h5, hlam]
                                    · linarith only [h37, h8, hlam]
                                  · linarith only [h36, h6, hlam]
                                · linarith only [h1, h35, hlam]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                rcases p14_3 (m.d 0 1) (by simp) with h42 | h42
                                · rcases p14_3 (m.d 1 2) (by simp) with h43 | h43
                                  · rcases p14_3 (m.d 1 3) (by simp) with h44 | h44
                                    · linarith only [h44, h5, hlam]
                                    · linarith only [h44, h9, hlam]
                                  · linarith only [h43, h7, hlam]
                                · linarith only [h2, h42, hlam]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h0, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h5, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h0, h10, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p14_1, u2ehi4]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p14_1, u2ehi4]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h1, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h6, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h8, hlam, p14_1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h7, hlam, hphi, ht23, ht34, p14_1, u2ehi4, u4elo1]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h2, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h7, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h9, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [h10, hlam, p14_0]
                              · have p14_0 := h14c.1
                                have p14_1 := h14c.2.1
                                have p14_2 := h14c.2.2.1
                                have p14_3 := h14c.2.2.2
                                linarith only [hlam, p14_0]
                            · linarith only [h1, h10, h13, hc34, hlam, hphi, u4elo0]
                          · linarith only [h1, h10, h12, hc24, hlam, hphi, u4elo0]
                        · linarith only [h0, h11, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h6, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                      · linarith only [h68, h8, h9, hlam]
                      · linarith only [h6, h68, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                  · linarith only [h5, h8, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                · linarith only [h4, h5, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h5, h6, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
              · linarith only [h5, h74, hc23, hlam, hphi, u2ehi3]
              · linarith only [h74, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
          · linarith only [h3, h4, hc25, hlam, hphi, u2ehi3]
        · linarith only [h3, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h79 | h79
        · rcases m.htr 0 2 5 (by decide) (by decide) with h80 | h80
          · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
            · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
              · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                    · linarith only [h0, h2, h85, hlam]
                    · linarith only [h0, h2, h82, h84, h85, hc35, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h81, h84, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                · linarith only [h80, h81, h83, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h81, h82, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
              · linarith only [h81, h91, hc23, hlam, hphi, u2ehi3]
              · linarith only [h91, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
          · linarith only [h79, h80, hc25, hlam, hphi, u2ehi3]
        · linarith only [h79, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
    · linarith only [h0, h1, hc13, hlam, hphi, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h97 | h97
    · rcases m.htr 0 1 5 (by decide) (by decide) with h98 | h98
      · rcases m.htr 0 2 4 (by decide) (by decide) with h99 | h99
        · rcases m.htr 0 2 5 (by decide) (by decide) with h100 | h100
          · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
            · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
              · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h108 | h108
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h109 | h109
                            · rcases h1bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p110_1, u2ehi1]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h0, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h0, h103, h106, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p110_1, u2ehi4]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h0, h103, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p110_1, u2ehi4]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h103, h106, h97, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p110_1, u2ehi4]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p110_1]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                rcases p110_3 (m.d 0 1) (by simp) with h119 | h119
                                · linarith only [h0, h101, h119, hlam]
                                · linarith only [h119, h97, hlam]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                rcases p110_3 (m.d 0 1) (by simp) with h122 | h122
                                · linarith only [h0, h101, h122, hlam]
                                · linarith only [h122, h98, hlam]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h101, h103, h106, h97, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p110_1, u2ehi4]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h101, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                rcases p110_3 (m.d 0 1) (by simp) with h128 | h128
                                · linarith only [h0, h128, hlam]
                                · linarith only [h128, h97, hlam]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                rcases p110_3 (m.d 0 1) (by simp) with h131 | h131
                                · linarith only [h0, h131, hlam]
                                · linarith only [h131, h98, hlam]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h97, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h102, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h104, hlam, p110_1]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h103, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p110_1, u2ehi4]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h98, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h103, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h105, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h106, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [hlam, p110_0]
                            · linarith only [h108, h109, hc34, hlam, hphi, u4elo2]
                          · linarith only [h0, h101, h106, h108, h97, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h101, h105, h107, h98, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h102, h106, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                    · linarith only [h0, h102, h105, h97, hc35, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h102, h104, h97, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h0, h100, h101, h103, h98, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h0, h100, h101, h102, h98, hc24, hlam, hphi, u2ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
              · linarith only [h101, h152, hc23, hlam, hphi, u2ehi3]
              · linarith only [h152, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
          · linarith only [h100, h99, hc25, hlam, hphi, u2ehi3]
        · linarith only [h99, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h157 | h157
        · rcases m.htr 0 2 5 (by decide) (by decide) with h158 | h158
          · rcases m.htr 1 2 3 (by decide) (by decide) with h159 | h159
            · rcases m.htr 1 2 4 (by decide) (by decide) with h160 | h160
              · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                      · linarith only [h164, h97, h98, hlam]
                      · linarith only [h160, h164, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                    · linarith only [h0, h160, h163, h97, hc35, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h160, h162, h97, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h158, h159, h161, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h0, h159, h160, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
              · linarith only [h159, h171, hc23, hlam, hphi, u2ehi3]
              · linarith only [h157, h171, hlam, hphi, ht23, ht34, u2ehi1, u4elo0]
          · linarith only [h157, h158, hc25, hlam, hphi, u2ehi3]
        · linarith only [h157, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h176 | h176
      · rcases m.htr 0 2 4 (by decide) (by decide) with h177 | h177
        · rcases m.htr 0 2 5 (by decide) (by decide) with h178 | h178
          · linarith only [h176, h178, h97, hlam, hphi, ht23, ht34, u2ehi4, u4elo1]
          · linarith only [h177, h178, hc25, hlam, hphi, u2ehi3]
        · linarith only [h177, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h182 | h182
        · rcases m.htr 0 2 5 (by decide) (by decide) with h183 | h183
          · rcases m.htr 1 2 3 (by decide) (by decide) with h184 | h184
            · rcases m.htr 1 2 4 (by decide) (by decide) with h185 | h185
              · rcases m.htr 1 2 5 (by decide) (by decide) with h186 | h186
                · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h188 | h188
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h191 | h191
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h192 | h192
                            · rcases h1bigk with h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h176, h189, hlam, hphi, ht23, ht34, p193_1, u2ehi1, u4elo1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h0, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h97, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h176, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                rcases p193_3 (m.d 0 1) (by simp) with h199 | h199
                                · linarith only [h199, hlam, p193_0]
                                · rcases p193_3 (m.d 1 2) (by simp) with h201 | h201
                                  · rcases p193_3 (m.d 1 3) (by simp) with h202 | h202
                                    · linarith only [h184, h202, hlam]
                                    · linarith only [h0, h202, hlam]
                                  · linarith only [h201, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h97, hc01, hc12, hlam, hphi, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h176, hc01, hc12, hlam, hphi, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                rcases p193_3 (m.d 0 1) (by simp) with h210 | h210
                                · linarith only [h210, hlam, p193_0]
                                · rcases p193_3 (m.d 1 2) (by simp) with h212 | h212
                                  · rcases p193_3 (m.d 1 3) (by simp) with h213 | h213
                                    · rcases p193_3 (m.d 1 4) (by simp) with h214 | h214
                                      · linarith only [h187, h214, hlam]
                                      · linarith only [h214, h97, hlam]
                                    · linarith only [h213, hlam, p193_0]
                                  · linarith only [h176, h189, h212, hlam, hphi, ht23, ht34, u2ehi1, u4elo1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h184, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h176, h189, hc01, hc13, hlam, hphi, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h176, h184, hc01, hc12, hlam, hphi, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p193_1, u4elo1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h185, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h187, hlam, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h176, h183, hlam, hphi, ht23, ht34, p193_1, u2ehi4, u4elo1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h189, hc01, hlam, hphi, ht12, ht23, ht34, p193_1, u4elo1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h186, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h188, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h189, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hlam, p193_0]
                            · linarith only [h182, h191, h192, h97, hc34, hlam, hphi, u4elo1]
                          · linarith only [h191, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                        · linarith only [h188, h189, h190, hlam, hphi, ht23, ht34, u2ehi2, u4elo1]
                      · linarith only [h189, h97, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                      · linarith only [h187, h188, h237, hlam]
                      · linarith only [h182, h237, h97, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                  · linarith only [h0, h187, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h183, h184, h186, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h184, h185, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
              · linarith only [h184, h243, hc23, hlam, hphi, u2ehi3]
              · linarith only [h243, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
          · linarith only [h182, h183, hc25, hlam, hphi, u2ehi3]
        · linarith only [h182, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]

end R2N4
