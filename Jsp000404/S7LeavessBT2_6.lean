import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sBT2_H_I_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have h2elo := hb2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · linarith only [h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · linarith only [h3, h5, h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h3, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h14, h5, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                          · linarith only [h16, h3, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · linarith only [h16, h3, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h13, h4, h5, hc12, hlam, hphi, u2elo4]
                    · linarith only [h12, h3, h5, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
                · linarith only [h21, h4, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h23 | h23
                  · linarith only [h23, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h27, h5, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                          · linarith only [h0, h29, h3, h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                            · linarith only [h2, h21, h31, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                              · linarith only [h23, h33, h4, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                                · linarith only [h29, h33, h35, h4, h5, hc23, hc34, hlam, hphi]
                                · rcases h0bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h29, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    rcases p37_3 (m.d 0 1) (by simp) with h40 | h40
                                    · rcases p37_3 (m.d 0 2) (by simp) with h41 | h41
                                      · linarith only [h0, h25, h41, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo4]
                                      · linarith only [h3, h41, hlam]
                                    · linarith only [h0, h40, hlam]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    rcases p37_3 (m.d 0 1) (by simp) with h45 | h45
                                    · rcases p37_3 (m.d 0 2) (by simp) with h46 | h46
                                      · linarith only [h1, h26, h29, h46, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo4]
                                      · linarith only [h4, h46, hlam]
                                    · linarith only [h1, h45, hlam]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht0b, ht5b, p37_1, u5ehi0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h5, hc01, hlam, hphi, ht12, p37_1, u2elo4]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h0, h25, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo4]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h1, h26, h29, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo4]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h5, hlam, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h0, hlam, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h3, hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h7, hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h21, hlam, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h1, hlam, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h4, hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h0, h25, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo4]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h23, hlam, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h2, hlam, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h2, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h0, h25, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo4]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p37_1, u2elo4]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hlam, p37_0]
                      · linarith only [h26, h4, hc12, hlam, hphi, u2elo0]
                    · linarith only [h25, h3, h5, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h73 | h73
            · linarith only [h4, h73, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
              · linarith only [h3, h4, h75, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                · linarith only [h3, h4, h77, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h79 | h79
                  · linarith only [h4, h79, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                      · linarith only [h4, h82, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
                        · linarith only [h3, h73, h82, h84, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                          · linarith only [h1, h3, h75, h82, h86, hc12, hlam, hphi, u2elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                            · linarith only [h3, h4, h77, h88, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                              · linarith only [h90, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                              · linarith only [h3, h4, h90, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h3, h4, h81, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h94 | h94
          · rcases m.htr 0 2 5 (by decide) (by decide) with h95 | h95
            · linarith only [h95, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h97 | h97
              · rcases m.htr 0 3 5 (by decide) (by decide) with h98 | h98
                · linarith only [h3, h98, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
                  · linarith only [h100, h3, h94, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                    · linarith only [h102, h3, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                        · linarith only [h105, h95, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                            · linarith only [h108, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h110 | h110
                              · linarith only [h100, h110, h2, h94, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                                · linarith only [h107, h108, h110, h112, h3, h94, hlam]
                                · linarith only [h108, h112, h3, h94, hc24, hc45, hlam, hphi]
                          · linarith only [h107, h3, h94, h97, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h104, h94, hc12, hlam, hphi, u2elo0]
              · linarith only [h3, h94, h97, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h118 | h118
            · linarith only [h118, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h120 | h120
              · rcases m.htr 0 3 5 (by decide) (by decide) with h121 | h121
                · linarith only [h121, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h123 | h123
                  · linarith only [h123, h94, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h125 | h125
                    · linarith only [h125, h3, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                      · linarith only [h127, h94, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                        · linarith only [h118, h125, h129, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                            · linarith only [h120, h121, h132, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                              · linarith only [h123, h131, h132, h134, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h136 | h136
                                · linarith only [h120, h136, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h0bigk with h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [hlam, p138_0]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    rcases p138_3 (m.d 0 1) (by simp) with h140 | h140
                                    · rcases p138_3 (m.d 0 2) (by simp) with h141 | h141
                                      · linarith only [h141, hlam, p138_0]
                                      · rcases p138_3 (m.d 0 3) (by simp) with h143 | h143
                                        · linarith only [h0, h143, hlam]
                                        · linarith only [h143, h3, hlam]
                                    · linarith only [h140, hlam, p138_0]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h120, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    rcases p138_3 (m.d 0 1) (by simp) with h148 | h148
                                    · rcases p138_3 (m.d 0 2) (by simp) with h149 | h149
                                      · linarith only [h1, h131, h149, h94, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p138_1, u2elo2]
                                      · rcases p138_3 (m.d 0 3) (by simp) with h151 | h151
                                        · linarith only [h0, h151, hlam]
                                        · linarith only [h120, h151, hlam]
                                    · linarith only [h1, h148, hlam]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p138_1, u5ehi1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, p138_1, u2elo0]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [hlam, p138_0]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h3, hlam, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h94, hlam, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h118, hlam, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h0, hlam, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h132, h136, h3, hc02, hc45, hlam, hphi, ht23, ht34, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [hlam, p138_0]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h1, h127, h132, h136, h3, hc12, hc45, hlam, hphi, ht23, ht34, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h121, hlam, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h1, hlam, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h131, h132, h136, h94, hc02, hc45, hlam, hphi, ht23, ht34, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h120, hlam, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [hlam, p138_0]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h123, hlam, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h2, hlam, p138_1]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h118, hc02, hlam, hphi, p138_1, u2elo4]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h118, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p138_1, u2elo4]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [h118, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p138_1, u2elo4]
                                  · have p138_0 := h138c.1
                                    have p138_1 := h138c.2.1
                                    have p138_2 := h138c.2.2.1
                                    have p138_3 := h138c.2.2.2
                                    linarith only [hlam, p138_0]
                          · linarith only [h120, h131, h3, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h177 | h177
                · linarith only [h120, h177, h94, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h179 | h179
                  · linarith only [h179, h94, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
                    · linarith only [h181, h3, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h183 | h183
                      · linarith only [h183, h94, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                        · linarith only [h118, h181, h185, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                          · linarith only [h120, h187, h3, hc02, hlam, hphi, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h189 | h189
                            · linarith only [h177, h187, h189, hc03, hc34, hlam, hphi]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h191 | h191
                              · linarith only [h191, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
                                · linarith only [h187, h191, h193, h3, hc02, hc34, hlam, hphi, ht23]
                                · linarith only [h187, h193, h3, hc02, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h196 | h196
        · rcases m.htr 0 2 4 (by decide) (by decide) with h197 | h197
          · rcases m.htr 0 2 5 (by decide) (by decide) with h198 | h198
            · linarith only [h198, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h200 | h200
              · rcases m.htr 0 3 5 (by decide) (by decide) with h201 | h201
                · linarith only [h0, h198, h2, h201, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h203 | h203
                  · linarith only [h196, h198, h200, h203, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h205 | h205
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h206 | h206
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h207 | h207
                        · linarith only [h198, h207, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h209 | h209
                          · linarith only [h0, h2, h205, h207, h209, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · linarith only [h0, h2, h200, h207, h209, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h197, h206, hc12, hlam, hphi, u2elo0]
                    · linarith only [h196, h198, h205, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h214 | h214
                · linarith only [h197, h198, h200, h214, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
                  · linarith only [h197, h198, h216, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h218 | h218
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h220 | h220
                        · linarith only [h198, h220, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h222 | h222
                          · linarith only [h196, h200, h222, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h224 | h224
                            · linarith only [h214, h224, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h226 | h226
                              · linarith only [h1, h2, h216, h219, h220, h226, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h228 | h228
                                · linarith only [h0, h2, h220, h226, h228, hc13, hc34, hlam, hphi]
                                · rcases h0bigk with h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [hlam, p230_0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p230_1]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h2, h220, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p230_1, u2elo4]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h2, h220, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p230_1, u2elo4]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h2, hlam, p230_0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, p230_1, u2elo0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [hlam, p230_0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h0, h218, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p230_1, u2elo0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h0, h200, h218, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p230_1, u2elo0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h198, hlam, p230_1]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h0, hlam, p230_1]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h196, hlam, p230_0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [hlam, p230_0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h200, hlam, p230_0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h214, hlam, p230_1]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h1, hlam, p230_1]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h197, hlam, p230_0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h0, h1, h2, h218, h220, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p230_1, u2elo4]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [hlam, p230_0]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h216, hlam, p230_1]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h0, h218, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p230_1]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h2, h220, hc02, hlam, hphi, p230_1, u2elo4]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h0, h2, h218, h220, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p230_1, u2elo4]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [h2, h220, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p230_1, u2elo4]
                                  · have p230_0 := h230c.1
                                    have p230_1 := h230c.2.1
                                    have p230_2 := h230c.2.2.1
                                    have p230_3 := h230c.2.2.2
                                    linarith only [hlam, p230_0]
                      · linarith only [h197, h219, hc12, hlam, hphi, u2elo0]
                    · linarith only [h196, h198, h218, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h258 | h258
            · linarith only [h197, h258, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h260 | h260
              · linarith only [h196, h197, h260, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h262 | h262
                · linarith only [h196, h197, h262, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h264 | h264
                  · linarith only [h1, h2, h264, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                      · linarith only [h197, h267, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h269 | h269
                        · linarith only [h1, h2, h258, h267, h269, hlam]
                        · linarith only [h1, h2, h267, h269, hc12, hlam, hphi, u2elo4]
                    · linarith only [h196, h266, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h273 | h273
          · rcases m.htr 0 2 5 (by decide) (by decide) with h274 | h274
            · linarith only [h196, h274, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h276 | h276
              · rcases m.htr 0 3 5 (by decide) (by decide) with h277 | h277
                · linarith only [h0, h2, h277, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h279 | h279
                  · linarith only [h196, h273, h279, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
                    · linarith only [h196, h281, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h283 | h283
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h284 | h284
                        · linarith only [h0, h2, h274, h281, h284, hlam]
                        · linarith only [h0, h2, h281, h284, hc12, hlam, hphi, u2elo4]
                      · linarith only [h196, h273, h283, hc12, hlam, hphi, u2elo2]
              · linarith only [h196, h273, h276, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h289 | h289
            · linarith only [h0, h196, h2, h289, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h291 | h291
              · rcases m.htr 0 3 5 (by decide) (by decide) with h292 | h292
                · linarith only [h0, h2, h289, h292, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h294 | h294
                  · linarith only [h1, h2, h289, h294, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
                    · linarith only [h196, h296, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                      · linarith only [h0, h2, h273, h289, h296, h298, hc02, hlam, hphi, u2elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h300 | h300
                        · linarith only [h0, h2, h289, h296, h300, hlam]
                        · linarith only [h0, h2, h296, h300, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h303 | h303
                · linarith only [h1, h2, h291, h303, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h305 | h305
                  · linarith only [h1, h2, h289, h305, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
                    · linarith only [h196, h307, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h309 | h309
                      · linarith only [h273, h307, h309, hc02, hlam, hphi, u2elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
                        · linarith only [h0, h2, h289, h307, h311, hlam]
                        · linarith only [h0, h2, h307, h311, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h314 | h314
      · linarith only [h1, h314, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h316 | h316
        · rcases m.htr 0 2 4 (by decide) (by decide) with h317 | h317
          · rcases m.htr 0 2 5 (by decide) (by decide) with h318 | h318
            · linarith only [h318, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h320 | h320
              · linarith only [h0, h1, h320, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h322 | h322
                · linarith only [h0, h1, h317, h318, h322, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h324 | h324
                  · linarith only [h317, h318, h324, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h327 | h327
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h328 | h328
                        · linarith only [h1, h317, h318, h328, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h1, h326, h327, h328, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h317, h327, hc12, hlam, hphi, u2elo0]
                    · linarith only [h316, h318, h326, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h333 | h333
            · linarith only [h317, h333, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h335 | h335
              · linarith only [h0, h1, h335, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h337 | h337
                · linarith only [h316, h317, h337, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h339 | h339
                  · linarith only [h317, h339, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
                      · linarith only [h317, h342, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                        · linarith only [h316, h333, h342, h344, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h346 | h346
                          · linarith only [h0, h1, h335, h341, h342, h346, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h348 | h348
                            · linarith only [h0, h1, h337, h341, h342, h348, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h350 | h350
                              · linarith only [h350, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                              · linarith only [h0, h1, h342, h350, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h316, h317, h341, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h354 | h354
          · linarith only [h0, h1, h316, h354, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h356 | h356
            · linarith only [h0, h1, h316, h356, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h358 | h358
              · linarith only [h0, h1, h358, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h360 | h360
                · linarith only [h0, h1, h354, h360, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h362 | h362
                  · linarith only [h354, h362, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h364 | h364
                    · linarith only [h316, h364, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h366 | h366
                      · linarith only [h0, h1, h362, h364, h366, hc24, hc45, hlam, hphi]
                      · linarith only [h0, h1, h364, h366, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h369 | h369
    · rcases m.htr 0 1 5 (by decide) (by decide) with h370 | h370
      · linarith only [h0, h370, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h372 | h372
        · rcases m.htr 0 2 4 (by decide) (by decide) with h373 | h373
          · rcases m.htr 0 2 5 (by decide) (by decide) with h374 | h374
            · linarith only [h374, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h376 | h376
              · rcases m.htr 0 3 5 (by decide) (by decide) with h377 | h377
                · linarith only [h372, h374, h377, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h379 | h379
                  · linarith only [h0, h369, h372, h374, h379, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h381 | h381
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h382 | h382
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h383 | h383
                        · linarith only [h0, h372, h374, h383, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h369, h381, h382, h383, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h0, h369, h381, h382, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h372, h374, h381, hc12, hlam, hphi, u2elo4]
              · linarith only [h0, h369, h376, hlam]
          · linarith only [h0, h369, h372, h373, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h390 | h390
          · rcases m.htr 0 2 5 (by decide) (by decide) with h391 | h391
            · linarith only [h372, h391, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h393 | h393
              · rcases m.htr 0 3 5 (by decide) (by decide) with h394 | h394
                · linarith only [h372, h394, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h396 | h396
                  · linarith only [h390, h391, h396, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                    · linarith only [h372, h398, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h400 | h400
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h401 | h401
                        · linarith only [h391, h398, h401, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h403 | h403
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h404 | h404
                            · linarith only [h0, h369, h394, h400, h403, h404, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h406 | h406
                              · linarith only [h369, h396, h400, h406, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h408 | h408
                                · linarith only [h0, h369, h398, h400, h403, h404, h406, h408, hlam]
                                · linarith only [h0, h369, h398, h404, h408, hc14, hc45, hlam, hphi]
                          · linarith only [h0, h369, h393, h398, h400, h403, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h372, h390, h400, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h369, h393, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h414 | h414
            · linarith only [h372, h414, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h416 | h416
              · rcases m.htr 0 3 5 (by decide) (by decide) with h417 | h417
                · linarith only [h372, h417, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h419 | h419
                  · linarith only [h0, h369, h414, h417, h419, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
                    · linarith only [h372, h421, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                      · linarith only [h390, h421, h423, hc02, hlam, hphi, u2elo2]
                      · linarith only [h0, h369, h421, h423, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h369, h416, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h427 | h427
      · linarith only [h0, h427, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h429 | h429
        · rcases m.htr 0 2 4 (by decide) (by decide) with h430 | h430
          · rcases m.htr 0 2 5 (by decide) (by decide) with h431 | h431
            · linarith only [h431, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h433 | h433
              · rcases m.htr 0 3 5 (by decide) (by decide) with h434 | h434
                · linarith only [h429, h431, h434, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
                  · linarith only [h429, h431, h433, h436, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h438 | h438
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
                        · linarith only [h369, h429, h431, h433, h440, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h438, h440, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h438, h439, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h429, h431, h438, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h445 | h445
                · linarith only [h433, h445, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h447 | h447
                  · linarith only [h430, h431, h447, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h449 | h449
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h450 | h450
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h451 | h451
                        · linarith only [h431, h451, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h449, h451, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h449, h450, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h429, h431, h449, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h456 | h456
            · linarith only [h430, h456, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h458 | h458
              · linarith only [h429, h430, h458, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h460 | h460
                · linarith only [h429, h430, h460, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h462 | h462
                  · linarith only [h430, h462, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h464 | h464
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h465 | h465
                      · linarith only [h430, h465, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h464, h465, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h429, h464, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h469 | h469
          · rcases m.htr 0 2 5 (by decide) (by decide) with h470 | h470
            · linarith only [h429, h470, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h472 | h472
              · rcases m.htr 0 3 5 (by decide) (by decide) with h473 | h473
                · linarith only [h429, h473, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h475 | h475
                  · linarith only [h429, h469, h475, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
                    · linarith only [h429, h477, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
                      · linarith only [h369, h477, h479, hc01, hlam, hphi, ht12, u2elo2]
                      · linarith only [h469, h479, hc12, hlam, hphi, u2elo0]
              · linarith only [h429, h469, h472, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h483 | h483
            · linarith only [h429, h483, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h485 | h485
              · rcases m.htr 0 3 5 (by decide) (by decide) with h486 | h486
                · linarith only [h429, h486, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
                  · linarith only [h469, h488, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
                    · linarith only [h429, h490, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h492 | h492
                      · linarith only [h469, h490, h492, hc02, hlam, hphi, u2elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h494 | h494
                        · linarith only [h483, h490, h494, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h496 | h496
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h497 | h497
                            · linarith only [h485, h486, h497, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h499 | h499
                              · linarith only [h488, h496, h497, h499, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h501 | h501
                                · linarith only [h485, h492, h499, h501, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h0bigk with h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [hlam, p503_0]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h369, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h0, hlam, p503_0]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h369, hlam, p503_0]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h427, hlam, p503_0]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, p503_1, u2elo0]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [hlam, p503_0]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h429, hlam, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h469, hlam, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h483, hlam, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h0, h490, h497, h501, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h0, h490, h497, h501, hc02, hc45, hlam, hphi, ht23, ht34, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [hlam, p503_0]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h0, h490, h497, h501, hc04, hc45, hlam, hphi, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h486, hlam, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h369, h492, h496, h497, h501, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h369, h492, h496, h497, h501, hc02, hc45, hlam, hphi, ht23, ht34, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h485, hlam, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [hlam, p503_0]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h488, hlam, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h427, hc01, hc15, hlam, hphi, p503_1]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h427, h494, hc02, hlam, hphi, p503_1, u2elo4]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h427, h494, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p503_1, u2elo4]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [h369, h427, h492, h494, h496, h497, h501, hc01, hc04, hc45, hlam, hphi, ht12, p503_1, u2elo4]
                                  · have p503_0 := h503c.1
                                    have p503_1 := h503c.2.1
                                    have p503_2 := h503c.2.2.1
                                    have p503_3 := h503c.2.2.2
                                    linarith only [hlam, p503_0]
                          · linarith only [h0, h485, h490, h496, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h530 | h530
                · linarith only [h469, h485, h530, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h532 | h532
                  · linarith only [h469, h532, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h534 | h534
                    · linarith only [h429, h534, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h536 | h536
                      · linarith only [h469, h534, h536, hc02, hlam, hphi, u2elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h538 | h538
                        · linarith only [h534, h538, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h540 | h540
                          · linarith only [h0, h485, h540, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h542 | h542
                            · linarith only [h530, h540, h542, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h544 | h544
                              · linarith only [h544, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h546 | h546
                                · linarith only [h534, h540, h544, h546, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h534, h540, h546, hc01, hc45, hlam, hphi, ht12, ht23, ht34]

theorem n7l_sBT2_H_I_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
                · linarith only [h5, h9, hlam]
                · linarith only [h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h8, hlam, p0_0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
              · rcases m.htr 0 1 3 (by decide) (by decide) with h16 | h16
                · linarith only [h16, h5, hlam]
                · linarith only [h16, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h15, hlam, p0_0]
            · linarith only [h14, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases m.htr 0 1 2 (by decide) (by decide) with h23 | h23
              · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
                · rcases m.htr 0 1 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h21, h25, hlam]
                  · linarith only [h25, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h23, h24, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h23, hlam, p0_0]
            · linarith only [h22, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h31 | h31
            · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
              · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                · rcases m.htr 0 1 4 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h31, h35, hlam]
                    · linarith only [h35, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h32, h34, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h32, h33, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h32, hlam, p0_0]
            · linarith only [h31, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · rcases p0_3 (m.d 0 2) (by simp) with h44 | h44
      · rcases p0_3 (m.d 0 3) (by simp) with h45 | h45
        · linarith only [h45, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h47 | h47
          · rcases p0_3 (m.d 0 5) (by simp) with h48 | h48
            · rcases m.htr 0 1 2 (by decide) (by decide) with h49 | h49
              · linarith only [h44, h49, hlam]
              · linarith only [h49, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h48, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h44, h54, hlam]
              · linarith only [h54, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h53, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h58 | h58
        · linarith only [h58, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 0 5) (by simp) with h61 | h61
            · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
              · rcases m.htr 0 1 3 (by decide) (by decide) with h63 | h63
                · rcases m.htr 0 1 4 (by decide) (by decide) with h64 | h64
                  · linarith only [h60, h64, hlam]
                  · linarith only [h44, h64, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h63, hlam, p0_0]
              · linarith only [h44, h62, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h61, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h70 | h70
            · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
              · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h70, h74, hlam]
                    · linarith only [h74, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h44, h71, h73, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h72, hlam, p0_0]
              · linarith only [h44, h71, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h70, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h43, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h82 | h82
    · rcases p0_3 (m.d 0 2) (by simp) with h83 | h83
      · rcases p0_3 (m.d 0 3) (by simp) with h84 | h84
        · rcases p0_3 (m.d 0 4) (by simp) with h85 | h85
          · linarith only [h85, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h87 | h87
            · rcases m.htr 0 1 2 (by decide) (by decide) with h88 | h88
              · linarith only [h83, h88, hlam]
              · linarith only [h88, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h87, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h92 | h92
          · linarith only [h92, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h94 | h94
            · rcases m.htr 0 1 2 (by decide) (by decide) with h95 | h95
              · linarith only [h83, h95, hlam]
              · linarith only [h84, h95, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h94, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h99 | h99
        · rcases p0_3 (m.d 0 4) (by simp) with h100 | h100
          · linarith only [h100, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h102 | h102
            · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
              · rcases m.htr 0 1 3 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h99, hlam]
                · linarith only [h104, h83, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h103, h83, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h102, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h109 | h109
          · linarith only [h109, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h111 | h111
            · rcases m.htr 0 1 2 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 1 3 (by decide) (by decide) with h113 | h113
                · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h115 | h115
                    · linarith only [h111, h115, hlam]
                    · linarith only [h115, h99, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h114, hlam, p0_0]
                · linarith only [h112, h113, h83, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h83, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h111, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h82, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h124 | h124
    · linarith only [h124, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h126 | h126
      · rcases p0_3 (m.d 0 3) (by simp) with h127 | h127
        · rcases p0_3 (m.d 0 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 0 5) (by simp) with h129 | h129
            · rcases m.htr 0 1 2 (by decide) (by decide) with h130 | h130
              · linarith only [h130, hlam, p0_0]
              · linarith only [h130, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h129, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
            · rcases m.htr 0 1 2 (by decide) (by decide) with h135 | h135
              · linarith only [h135, hlam, p0_0]
              · linarith only [h135, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h134, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
          · rcases p0_3 (m.d 0 5) (by simp) with h140 | h140
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · linarith only [h141, hlam, p0_0]
              · linarith only [h141, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h140, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h145 | h145
            · rcases m.htr 0 1 2 (by decide) (by decide) with h146 | h146
              · linarith only [h146, hlam, p0_0]
              · linarith only [h146, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h145, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h126, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h152 | h152
    · rcases p0_3 (m.d 0 2) (by simp) with h153 | h153
      · rcases p0_3 (m.d 0 3) (by simp) with h154 | h154
        · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h156 | h156
          · rcases p0_3 (m.d 0 5) (by simp) with h157 | h157
            · rcases m.htr 0 1 2 (by decide) (by decide) with h158 | h158
              · rcases m.htr 0 1 3 (by decide) (by decide) with h159 | h159
                · rcases m.htr 0 1 4 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h162 | h162
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h163 | h163
                        · linarith only [h156, h163, hlam]
                        · linarith only [h163, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h162, hlam, p0_0]
                    · linarith only [h158, h159, h161, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h158, h159, h160, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h158, h159, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h158, hlam]
            · linarith only [h157, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h172 | h172
            · rcases m.htr 0 1 2 (by decide) (by decide) with h173 | h173
              · rcases m.htr 0 1 3 (by decide) (by decide) with h174 | h174
                · rcases m.htr 0 1 4 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h177 | h177
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h178 | h178
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h179 | h179
                          · linarith only [h172, h179, hlam]
                          · linarith only [h179, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h174, h178, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h177, hlam, p0_0]
                    · linarith only [h173, h174, h176, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h173, h174, h175, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h173, h174, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h173, hlam]
            · linarith only [h152, h172, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h153, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h190 | h190
      · rcases p0_3 (m.d 0 3) (by simp) with h191 | h191
        · linarith only [h191, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h193 | h193
          · rcases p0_3 (m.d 0 5) (by simp) with h194 | h194
            · rcases m.htr 0 1 2 (by decide) (by decide) with h195 | h195
              · linarith only [h152, h195, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h195, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h194, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h199 | h199
            · rcases m.htr 0 1 2 (by decide) (by decide) with h200 | h200
              · linarith only [h152, h200, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h200, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h199, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h190, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h205 | h205
    · rcases p0_3 (m.d 0 2) (by simp) with h206 | h206
      · rcases p0_3 (m.d 0 3) (by simp) with h207 | h207
        · rcases p0_3 (m.d 0 4) (by simp) with h208 | h208
          · linarith only [h208, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h210 | h210
            · rcases m.htr 0 1 2 (by decide) (by decide) with h211 | h211
              · rcases m.htr 0 1 3 (by decide) (by decide) with h212 | h212
                · rcases m.htr 0 1 4 (by decide) (by decide) with h213 | h213
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h214 | h214
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h215 | h215
                      · linarith only [h207, h215, hlam]
                      · linarith only [h215, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h211, h213, h214, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h211, h213, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h211, h212, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h205, h211, hlam]
            · linarith only [h210, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h223 | h223
          · linarith only [h223, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h225 | h225
            · rcases m.htr 0 1 2 (by decide) (by decide) with h226 | h226
              · rcases m.htr 0 1 3 (by decide) (by decide) with h227 | h227
                · rcases m.htr 0 1 4 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h230 | h230
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h231 | h231
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h232 | h232
                          · linarith only [h225, h232, hlam]
                          · linarith only [h207, h232, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h231, hlam, p0_0]
                      · linarith only [h207, h227, h230, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h207, h226, h227, h229, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h207, h226, h227, h228, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h207, h226, h227, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h205, h226, hlam]
            · linarith only [h225, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h206, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h243 | h243
      · rcases p0_3 (m.d 0 3) (by simp) with h244 | h244
        · rcases p0_3 (m.d 0 4) (by simp) with h245 | h245
          · linarith only [h245, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h247 | h247
            · rcases m.htr 0 1 2 (by decide) (by decide) with h248 | h248
              · linarith only [h205, h248, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h205, h248, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h247, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h252 | h252
          · linarith only [h252, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h254 | h254
            · rcases m.htr 0 1 2 (by decide) (by decide) with h255 | h255
              · linarith only [h205, h255, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h205, h255, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h254, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h243, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h261 | h261
    · linarith only [h261, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h263 | h263
      · rcases p0_3 (m.d 0 3) (by simp) with h264 | h264
        · rcases p0_3 (m.d 0 4) (by simp) with h265 | h265
          · rcases p0_3 (m.d 0 5) (by simp) with h266 | h266
            · rcases m.htr 0 1 2 (by decide) (by decide) with h267 | h267
              · linarith only [h267, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h267, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h263, h266, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h271 | h271
            · rcases m.htr 0 1 2 (by decide) (by decide) with h272 | h272
              · linarith only [h263, h272, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h272, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h263, h271, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h264, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h277 | h277
        · rcases p0_3 (m.d 0 4) (by simp) with h278 | h278
          · rcases p0_3 (m.d 0 5) (by simp) with h279 | h279
            · rcases m.htr 0 1 2 (by decide) (by decide) with h280 | h280
              · linarith only [h280, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h280, hlam]
            · linarith only [h279, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h284 | h284
            · rcases m.htr 0 1 2 (by decide) (by decide) with h285 | h285
              · linarith only [h285, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h285, hlam]
            · linarith only [h284, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h277, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h290 | h290
    · rcases p0_3 (m.d 0 2) (by simp) with h291 | h291
      · linarith only [h291, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h293 | h293
        · rcases p0_3 (m.d 0 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 0 5) (by simp) with h295 | h295
            · rcases m.htr 0 1 2 (by decide) (by decide) with h296 | h296
              · rcases m.htr 0 1 3 (by decide) (by decide) with h297 | h297
                · rcases m.htr 0 1 4 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h300 | h300
                      · linarith only [h300, hlam, p0_0]
                      · linarith only [h300, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h296, h297, h299, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h296, h297, h298, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h290, h297, hlam]
              · linarith only [h290, h296, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h290, h295, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h308 | h308
            · rcases m.htr 0 1 2 (by decide) (by decide) with h309 | h309
              · rcases m.htr 0 1 3 (by decide) (by decide) with h310 | h310
                · rcases m.htr 0 1 4 (by decide) (by decide) with h311 | h311
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h312 | h312
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
                      · linarith only [h313, hlam, p0_0]
                      · linarith only [h313, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h309, h310, h312, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h309, h310, h311, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h290, h310, hlam]
              · linarith only [h290, h309, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h290, h308, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h293, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h322 | h322
      · linarith only [h322, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h324 | h324
        · rcases p0_3 (m.d 0 4) (by simp) with h325 | h325
          · rcases p0_3 (m.d 0 5) (by simp) with h326 | h326
            · rcases m.htr 0 1 2 (by decide) (by decide) with h327 | h327
              · linarith only [h290, h327, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h329 | h329
                · linarith only [h327, h329, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h327, h329, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h326, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h333 | h333
            · rcases m.htr 0 1 2 (by decide) (by decide) with h334 | h334
              · linarith only [h290, h334, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h336 | h336
                · linarith only [h334, h336, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h334, h336, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h333, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h324, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h342 | h342
    · rcases p0_3 (m.d 0 2) (by simp) with h343 | h343
      · rcases p0_3 (m.d 0 3) (by simp) with h344 | h344
        · rcases p0_3 (m.d 0 4) (by simp) with h345 | h345
          · linarith only [h345, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h347 | h347
            · rcases m.htr 0 1 2 (by decide) (by decide) with h348 | h348
              · rcases m.htr 0 1 3 (by decide) (by decide) with h349 | h349
                · rcases m.htr 0 1 4 (by decide) (by decide) with h350 | h350
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h351 | h351
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h352 | h352
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h353 | h353
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h354 | h354
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
                              · linarith only [h347, h356, hlam]
                              · linarith only [h350, h356, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                            · linarith only [h355, hlam, p0_0]
                          · linarith only [h350, h352, h354, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                        · linarith only [h350, h352, h353, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h343, h352, hlam]
                    · linarith only [h349, h350, h351, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h349, h350, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h342, h349, hlam]
              · linarith only [h342, h348, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h342, h347, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h344, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h369 | h369
        · rcases p0_3 (m.d 0 4) (by simp) with h370 | h370
          · linarith only [h370, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h372 | h372
            · rcases m.htr 0 1 2 (by decide) (by decide) with h373 | h373
              · rcases m.htr 0 1 3 (by decide) (by decide) with h374 | h374
                · rcases m.htr 0 1 4 (by decide) (by decide) with h375 | h375
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h376 | h376
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h377 | h377
                      · linarith only [h343, h374, h377, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h343, h373, h377, hc12, hc23, hlam, hphi, p0_1]
                    · linarith only [h343, h373, h374, h376, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h343, h373, h374, h375, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h342, h374, hlam]
              · linarith only [h342, h343, h373, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h342, h372, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h369, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h386 | h386
      · rcases p0_3 (m.d 0 3) (by simp) with h387 | h387
        · rcases p0_3 (m.d 0 4) (by simp) with h388 | h388
          · linarith only [h388, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h390 | h390
            · rcases m.htr 0 1 2 (by decide) (by decide) with h391 | h391
              · linarith only [h342, h391, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h342, h386, h391, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h386, h390, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h387, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h396 | h396
        · rcases p0_3 (m.d 0 4) (by simp) with h397 | h397
          · linarith only [h397, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h399 | h399
            · rcases m.htr 0 1 2 (by decide) (by decide) with h400 | h400
              · linarith only [h342, h400, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h402 | h402
                · linarith only [h386, h400, h402, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h386, h400, h402, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h399, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h396, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h408 | h408
    · linarith only [h408, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h410 | h410
      · rcases p0_3 (m.d 0 3) (by simp) with h411 | h411
        · rcases p0_3 (m.d 0 4) (by simp) with h412 | h412
          · rcases p0_3 (m.d 0 5) (by simp) with h413 | h413
            · rcases m.htr 0 1 2 (by decide) (by decide) with h414 | h414
              · linarith only [h410, h414, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h414, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h410, h413, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h412, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h419 | h419
          · rcases p0_3 (m.d 0 5) (by simp) with h420 | h420
            · rcases m.htr 0 1 2 (by decide) (by decide) with h421 | h421
              · linarith only [h410, h421, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h421, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h410, h420, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h419, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h426 | h426
        · rcases p0_3 (m.d 0 4) (by simp) with h427 | h427
          · rcases p0_3 (m.d 0 5) (by simp) with h428 | h428
            · rcases m.htr 0 1 2 (by decide) (by decide) with h429 | h429
              · linarith only [h429, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h429, hlam]
            · linarith only [h428, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h427, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h434 | h434
          · rcases p0_3 (m.d 0 5) (by simp) with h435 | h435
            · rcases m.htr 0 1 2 (by decide) (by decide) with h436 | h436
              · linarith only [h436, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h436, hlam]
            · linarith only [h435, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h434, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h441 | h441
    · rcases p0_3 (m.d 0 2) (by simp) with h442 | h442
      · linarith only [h442, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h444 | h444
        · rcases p0_3 (m.d 0 4) (by simp) with h445 | h445
          · rcases p0_3 (m.d 0 5) (by simp) with h446 | h446
            · rcases m.htr 0 1 2 (by decide) (by decide) with h447 | h447
              · rcases m.htr 0 1 3 (by decide) (by decide) with h448 | h448
                · rcases m.htr 0 1 4 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h450 | h450
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h451 | h451
                      · linarith only [h444, h448, h451, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h444, h451, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h447, h449, h450, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h441, h449, hlam]
                · linarith only [h441, h447, h448, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h441, h447, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h441, h446, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h445, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h460 | h460
          · rcases p0_3 (m.d 0 5) (by simp) with h461 | h461
            · rcases m.htr 0 1 2 (by decide) (by decide) with h462 | h462
              · rcases m.htr 0 1 3 (by decide) (by decide) with h463 | h463
                · rcases m.htr 0 1 4 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h465 | h465
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h466 | h466
                      · linarith only [h464, h466, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h444, h466, hlam]
                    · linarith only [h464, h465, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h441, h464, hlam]
                · linarith only [h441, h462, h463, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h441, h462, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h441, h461, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h460, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h475 | h475
      · linarith only [h475, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h477 | h477
        · rcases p0_3 (m.d 0 4) (by simp) with h478 | h478
          · rcases p0_3 (m.d 0 5) (by simp) with h479 | h479
            · rcases m.htr 0 1 2 (by decide) (by decide) with h480 | h480
              · linarith only [h441, h480, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h482 | h482
                · linarith only [h480, h482, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h477, h480, h482, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h479, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h478, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h487 | h487
          · rcases p0_3 (m.d 0 5) (by simp) with h488 | h488
            · rcases m.htr 0 1 2 (by decide) (by decide) with h489 | h489
              · linarith only [h441, h489, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h491 | h491
                · linarith only [h489, h491, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h493 | h493
                  · linarith only [h489, h493, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h489, h493, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h488, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h487, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h498 | h498
    · rcases p0_3 (m.d 0 2) (by simp) with h499 | h499
      · rcases p0_3 (m.d 0 3) (by simp) with h500 | h500
        · linarith only [h500, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h502 | h502
          · rcases p0_3 (m.d 0 5) (by simp) with h503 | h503
            · rcases m.htr 0 1 2 (by decide) (by decide) with h504 | h504
              · rcases m.htr 0 1 3 (by decide) (by decide) with h505 | h505
                · rcases m.htr 0 1 4 (by decide) (by decide) with h506 | h506
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h507 | h507
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h508 | h508
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h509 | h509
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h510 | h510
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h511 | h511
                            · linarith only [h511, hlam, p0_0]
                            · linarith only [h505, h511, hc13, hc34, hlam, hphi, p0_1]
                          · linarith only [h505, h509, h510, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h499, h509, hlam]
                      · linarith only [h499, h505, h508, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h505, h506, h507, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h498, h506, hlam]
                · linarith only [h498, h505, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h498, h504, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h498, h503, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h502, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h523 | h523
        · linarith only [h523, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h525 | h525
          · rcases p0_3 (m.d 0 5) (by simp) with h526 | h526
            · rcases m.htr 0 1 2 (by decide) (by decide) with h527 | h527
              · rcases m.htr 0 1 3 (by decide) (by decide) with h528 | h528
                · rcases m.htr 0 1 4 (by decide) (by decide) with h529 | h529
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h530 | h530
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h531 | h531
                      · linarith only [h499, h531, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h533 | h533
                        · linarith only [h529, h531, h533, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h527, h531, h533, hc12, hc24, hlam, hphi, p0_1]
                    · linarith only [h529, h530, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h498, h529, hlam]
                · linarith only [h498, h499, h527, h528, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h498, h499, h527, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h498, h526, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h525, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h542 | h542
      · rcases p0_3 (m.d 0 3) (by simp) with h543 | h543
        · linarith only [h543, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h545 | h545
          · rcases p0_3 (m.d 0 5) (by simp) with h546 | h546
            · rcases m.htr 0 1 2 (by decide) (by decide) with h547 | h547
              · linarith only [h498, h547, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h498, h542, h547, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h542, h546, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h545, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h552 | h552
        · linarith only [h552, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h554 | h554
          · rcases p0_3 (m.d 0 5) (by simp) with h555 | h555
            · rcases m.htr 0 1 2 (by decide) (by decide) with h556 | h556
              · linarith only [h498, h556, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h558 | h558
                · linarith only [h498, h558, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h560 | h560
                  · linarith only [h542, h556, h560, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h542, h556, h560, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h555, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h554, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h567 | h567
    · linarith only [h567, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h569 | h569
      · rcases p0_3 (m.d 0 3) (by simp) with h570 | h570
        · rcases p0_3 (m.d 0 4) (by simp) with h571 | h571
          · rcases p0_3 (m.d 0 5) (by simp) with h572 | h572
            · rcases m.htr 0 1 2 (by decide) (by decide) with h573 | h573
              · linarith only [h569, h573, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h573, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h572, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h577 | h577
            · rcases m.htr 0 1 2 (by decide) (by decide) with h578 | h578
              · linarith only [h569, h578, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h578, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h577, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h582 | h582
          · rcases p0_3 (m.d 0 5) (by simp) with h583 | h583
            · rcases m.htr 0 1 2 (by decide) (by decide) with h584 | h584
              · linarith only [h569, h584, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h584, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h583, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h588 | h588
            · rcases m.htr 0 1 2 (by decide) (by decide) with h589 | h589
              · linarith only [h569, h589, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h589, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h588, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h593 | h593
        · rcases p0_3 (m.d 0 4) (by simp) with h594 | h594
          · rcases p0_3 (m.d 0 5) (by simp) with h595 | h595
            · rcases m.htr 0 1 2 (by decide) (by decide) with h596 | h596
              · linarith only [h593, h596, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h596, hlam]
            · linarith only [h595, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h600 | h600
            · rcases m.htr 0 1 2 (by decide) (by decide) with h601 | h601
              · linarith only [h601, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h601, hlam]
            · linarith only [h600, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h605 | h605
          · rcases p0_3 (m.d 0 5) (by simp) with h606 | h606
            · rcases m.htr 0 1 2 (by decide) (by decide) with h607 | h607
              · linarith only [h607, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h607, hlam]
            · linarith only [h606, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h611 | h611
            · rcases m.htr 0 1 2 (by decide) (by decide) with h612 | h612
              · linarith only [h612, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h612, hlam]
            · linarith only [h611, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h616 | h616
    · rcases p0_3 (m.d 0 2) (by simp) with h617 | h617
      · linarith only [h617, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h619 | h619
        · rcases p0_3 (m.d 0 4) (by simp) with h620 | h620
          · rcases p0_3 (m.d 0 5) (by simp) with h621 | h621
            · rcases m.htr 0 1 2 (by decide) (by decide) with h622 | h622
              · rcases m.htr 0 1 3 (by decide) (by decide) with h623 | h623
                · rcases m.htr 0 1 4 (by decide) (by decide) with h624 | h624
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h625 | h625
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h626 | h626
                      · linarith only [h619, h623, h626, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h626, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h616, h625, hlam]
                  · linarith only [h616, h622, h624, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h622, h623, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h622, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h621, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h634 | h634
            · rcases m.htr 0 1 2 (by decide) (by decide) with h635 | h635
              · rcases m.htr 0 1 3 (by decide) (by decide) with h636 | h636
                · rcases m.htr 0 1 4 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h638 | h638
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h639 | h639
                      · linarith only [h619, h636, h639, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h639, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h616, h638, hlam]
                  · linarith only [h619, h635, h636, h637, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h635, h636, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h635, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h634, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h647 | h647
          · rcases p0_3 (m.d 0 5) (by simp) with h648 | h648
            · rcases m.htr 0 1 2 (by decide) (by decide) with h649 | h649
              · rcases m.htr 0 1 3 (by decide) (by decide) with h650 | h650
                · rcases m.htr 0 1 4 (by decide) (by decide) with h651 | h651
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h652 | h652
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h653 | h653
                      · linarith only [h647, h651, h653, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h653, hlam]
                    · linarith only [h616, h652, hlam]
                  · linarith only [h616, h651, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h649, h650, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h649, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h648, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h661 | h661
            · rcases m.htr 0 1 2 (by decide) (by decide) with h662 | h662
              · rcases m.htr 0 1 3 (by decide) (by decide) with h663 | h663
                · rcases m.htr 0 1 4 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h665 | h665
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h666 | h666
                      · linarith only [h665, h666, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h666, hlam]
                    · linarith only [h616, h665, hlam]
                  · linarith only [h616, h664, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h662, h663, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h662, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h661, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h674 | h674
      · linarith only [h674, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h676 | h676
        · rcases p0_3 (m.d 0 4) (by simp) with h677 | h677
          · rcases p0_3 (m.d 0 5) (by simp) with h678 | h678
            · rcases m.htr 0 1 2 (by decide) (by decide) with h679 | h679
              · linarith only [h616, h679, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h681 | h681
                · linarith only [h676, h679, h681, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h676, h679, h681, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h678, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h685 | h685
            · rcases m.htr 0 1 2 (by decide) (by decide) with h686 | h686
              · linarith only [h616, h686, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h688 | h688
                · linarith only [h676, h686, h688, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h676, h686, h688, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h685, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h692 | h692
          · rcases p0_3 (m.d 0 5) (by simp) with h693 | h693
            · rcases m.htr 0 1 2 (by decide) (by decide) with h694 | h694
              · linarith only [h616, h694, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h696 | h696
                · linarith only [h692, h694, h696, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h698 | h698
                  · linarith only [h692, h694, h698, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h692, h694, h698, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h693, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h702 | h702
            · rcases m.htr 0 1 2 (by decide) (by decide) with h703 | h703
              · linarith only [h616, h703, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h705 | h705
                · linarith only [h703, h705, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h707 | h707
                  · linarith only [h703, h707, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h709 | h709
                    · linarith only [h703, h709, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                    · linarith only [h703, h709, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h702, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h713 | h713
    · rcases p0_3 (m.d 0 2) (by simp) with h714 | h714
      · rcases p0_3 (m.d 0 3) (by simp) with h715 | h715
        · linarith only [h715, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h717 | h717
          · rcases p0_3 (m.d 0 5) (by simp) with h718 | h718
            · rcases m.htr 0 1 2 (by decide) (by decide) with h719 | h719
              · rcases m.htr 0 1 3 (by decide) (by decide) with h720 | h720
                · rcases m.htr 0 1 4 (by decide) (by decide) with h721 | h721
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h722 | h722
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h723 | h723
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h724 | h724
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h725 | h725
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h726 | h726
                            · linarith only [h717, h719, h724, h726, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                            · linarith only [h717, h726, hc03, hc34, hlam, hphi, p0_1]
                          · linarith only [h714, h725, hlam]
                        · linarith only [h714, h720, h724, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h714, h720, h723, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h713, h722, hlam]
                  · linarith only [h713, h720, h721, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h714, h719, h720, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h719, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h718, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h737 | h737
            · rcases m.htr 0 1 2 (by decide) (by decide) with h738 | h738
              · rcases m.htr 0 1 3 (by decide) (by decide) with h739 | h739
                · rcases m.htr 0 1 4 (by decide) (by decide) with h740 | h740
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h741 | h741
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h742 | h742
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h743 | h743
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h744 | h744
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h745 | h745
                            · linarith only [h738, h744, h745, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                            · linarith only [h717, h745, hlam]
                          · linarith only [h714, h744, hlam]
                        · linarith only [h714, h743, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h714, h739, h742, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h713, h741, hlam]
                  · linarith only [h713, h739, h740, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h714, h738, h739, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h738, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h737, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h756 | h756
        · linarith only [h756, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h758 | h758
          · rcases p0_3 (m.d 0 5) (by simp) with h759 | h759
            · rcases m.htr 0 1 2 (by decide) (by decide) with h760 | h760
              · rcases m.htr 0 1 3 (by decide) (by decide) with h761 | h761
                · rcases m.htr 0 1 4 (by decide) (by decide) with h762 | h762
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h763 | h763
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h764 | h764
                      · linarith only [h714, h764, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h766 | h766
                        · linarith only [h758, h762, h764, h766, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h758, h764, h766, hc02, hc24, hlam, hphi, p0_1]
                    · linarith only [h713, h763, hlam]
                  · linarith only [h713, h714, h760, h762, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h713, h714, h760, h761, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h714, h760, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h759, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h774 | h774
            · rcases m.htr 0 1 2 (by decide) (by decide) with h775 | h775
              · rcases m.htr 0 1 3 (by decide) (by decide) with h776 | h776
                · rcases m.htr 0 1 4 (by decide) (by decide) with h777 | h777
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h778 | h778
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h779 | h779
                      · linarith only [h714, h779, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h781 | h781
                        · linarith only [h778, h779, h781, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h783 | h783
                          · linarith only [h778, h779, h783, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                          · linarith only [h779, h783, hc02, hc25, hlam, hphi, p0_1]
                    · linarith only [h713, h778, hlam]
                  · linarith only [h713, h777, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h713, h714, h775, h776, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h714, h775, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h774, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h791 | h791
      · rcases p0_3 (m.d 0 3) (by simp) with h792 | h792
        · linarith only [h792, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h794 | h794
          · rcases p0_3 (m.d 0 5) (by simp) with h795 | h795
            · rcases m.htr 0 1 2 (by decide) (by decide) with h796 | h796
              · linarith only [h713, h791, h796, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h791, h796, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h795, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h800 | h800
            · rcases m.htr 0 1 2 (by decide) (by decide) with h801 | h801
              · linarith only [h713, h791, h801, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h791, h801, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h800, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h805 | h805
        · linarith only [h805, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h807 | h807
          · rcases p0_3 (m.d 0 5) (by simp) with h808 | h808
            · rcases m.htr 0 1 2 (by decide) (by decide) with h809 | h809
              · linarith only [h713, h807, h809, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h811 | h811
                · linarith only [h713, h811, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h813 | h813
                  · linarith only [h791, h807, h809, h813, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h791, h807, h809, h813, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h808, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h817 | h817
            · rcases m.htr 0 1 2 (by decide) (by decide) with h818 | h818
              · linarith only [h713, h818, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h820 | h820
                · linarith only [h713, h820, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h822 | h822
                  · linarith only [h791, h818, h822, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h824 | h824
                    · linarith only [h791, h818, h824, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                    · linarith only [h791, h818, h824, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h817, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h828 | h828
    · rcases p0_3 (m.d 0 2) (by simp) with h829 | h829
      · rcases p0_3 (m.d 0 3) (by simp) with h830 | h830
        · rcases p0_3 (m.d 0 4) (by simp) with h831 | h831
          · linarith only [h831, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h833 | h833
            · rcases m.htr 0 1 2 (by decide) (by decide) with h834 | h834
              · rcases m.htr 0 1 3 (by decide) (by decide) with h835 | h835
                · rcases m.htr 0 1 4 (by decide) (by decide) with h836 | h836
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h837 | h837
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h841 | h841
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h842 | h842
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h843 | h843
                                · linarith only [h843, hlam, p0_0]
                                · linarith only [h843, hc04, hc45, hlam, hphi, p0_1]
                              · linarith only [h830, h842, hlam]
                            · linarith only [h830, h836, h841, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                          · linarith only [h829, h840, hlam]
                        · linarith only [h829, h836, h839, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h829, h836, h838, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h828, h837, hlam]
                  · linarith only [h828, h836, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h829, h834, h835, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h828, h834, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h833, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h856 | h856
          · linarith only [h856, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h858 | h858
            · rcases m.htr 0 1 2 (by decide) (by decide) with h859 | h859
              · rcases m.htr 0 1 3 (by decide) (by decide) with h860 | h860
                · rcases m.htr 0 1 4 (by decide) (by decide) with h861 | h861
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h862 | h862
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h863 | h863
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h864 | h864
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h865 | h865
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h866 | h866
                            · linarith only [h830, h866, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h868 | h868
                              · linarith only [h859, h865, h866, h868, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                              · linarith only [h866, h868, hc03, hc35, hlam, hphi, p0_1]
                          · linarith only [h829, h865, hlam]
                        · linarith only [h829, h864, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h829, h830, h860, h863, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h828, h862, hlam]
                  · linarith only [h828, h830, h860, h861, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h829, h830, h859, h860, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h830, h859, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h858, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h879 | h879
        · rcases p0_3 (m.d 0 4) (by simp) with h880 | h880
          · linarith only [h880, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h882 | h882
            · rcases m.htr 0 1 2 (by decide) (by decide) with h883 | h883
              · rcases m.htr 0 1 3 (by decide) (by decide) with h884 | h884
                · rcases m.htr 0 1 4 (by decide) (by decide) with h885 | h885
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h886 | h886
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h887 | h887
                      · linarith only [h829, h879, h884, h887, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h829, h879, h887, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h828, h886, hlam]
                  · linarith only [h829, h879, h883, h884, h885, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h828, h829, h883, h884, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h829, h883, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h882, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h895 | h895
          · linarith only [h895, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h897 | h897
            · rcases m.htr 0 1 2 (by decide) (by decide) with h898 | h898
              · rcases m.htr 0 1 3 (by decide) (by decide) with h899 | h899
                · rcases m.htr 0 1 4 (by decide) (by decide) with h900 | h900
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h901 | h901
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h902 | h902
                      · linarith only [h829, h901, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h904 | h904
                        · linarith only [h829, h904, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h906 | h906
                          · linarith only [h879, h901, h902, h906, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                          · linarith only [h879, h902, h906, hc02, hc25, hlam, hphi, p0_1]
                    · linarith only [h828, h901, hlam]
                  · linarith only [h828, h829, h898, h900, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h828, h829, h898, h899, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h829, h898, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h897, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h914 | h914
      · rcases p0_3 (m.d 0 3) (by simp) with h915 | h915
        · rcases p0_3 (m.d 0 4) (by simp) with h916 | h916
          · linarith only [h916, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h918 | h918
            · rcases m.htr 0 1 2 (by decide) (by decide) with h919 | h919
              · linarith only [h828, h914, h919, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h914, h919, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h918, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h923 | h923
          · linarith only [h923, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h925 | h925
            · rcases m.htr 0 1 2 (by decide) (by decide) with h926 | h926
              · linarith only [h828, h914, h926, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h914, h926, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h925, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h930 | h930
        · rcases p0_3 (m.d 0 4) (by simp) with h931 | h931
          · linarith only [h931, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h933 | h933
            · rcases m.htr 0 1 2 (by decide) (by decide) with h934 | h934
              · linarith only [h828, h930, h934, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h936 | h936
                · linarith only [h914, h930, h934, h936, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h914, h930, h934, h936, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h933, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h940 | h940
          · linarith only [h940, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h942 | h942
            · rcases m.htr 0 1 2 (by decide) (by decide) with h943 | h943
              · linarith only [h828, h943, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h945 | h945
                · linarith only [h914, h943, h945, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h947 | h947
                  · linarith only [h828, h947, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h949 | h949
                    · linarith only [h914, h943, h949, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                    · linarith only [h914, h943, h949, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h942, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_L_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h3, h6, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 3 5 (by decide) (by decide) with h9 | h9
                · linarith only [h0, h3, h5, h9, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, h3, h5, h8, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h13, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h13, h3, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h16, h3, h5, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h18, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                    · linarith only [h0, h20, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h20, h3, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h23 | h23
            · linarith only [h1, h23, h3, h5, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h25 | h25
              · rcases m.htr 0 3 5 (by decide) (by decide) with h26 | h26
                · linarith only [h1, h26, h3, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
                  · linarith only [h1, h25, h28, h3, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                    · linarith only [h0, h3, h30, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                      · linarith only [h0, h23, h32, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                        · linarith only [h1, h34, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h25, h3, h30, h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h37 | h37
                · linarith only [h2, h25, h3, h37, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h39 | h39
                  · linarith only [h2, h3, h39, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                    · linarith only [h0, h3, h41, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                      · linarith only [h0, h23, h43, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                        · linarith only [h1, h25, h45, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
                          · linarith only [h1, h37, h47, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                            · linarith only [h2, h25, h3, h39, h49, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                                · linarith only [h2, h3, h41, h45, h47, h52, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h25, h5, h51, h52, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                                · linarith only [h0, h37, h5, h51, h55, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                                  · linarith only [h2, h3, h41, h45, h49, h57, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                                    · linarith only [h0, h5, h51, h57, h59, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h5, h51, h59, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h62 | h62
        · linarith only [h62, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h64 | h64
          · rcases m.htr 0 2 5 (by decide) (by decide) with h65 | h65
            · linarith only [h65, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h67 | h67
              · linarith only [h1, h2, h67, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
                · linarith only [h0, h64, h69, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
                  · linarith only [h71, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
                    · linarith only [h0, h2, h71, h73, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h2, h64, h71, h73, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h76 | h76
            · linarith only [h1, h64, h76, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h78 | h78
              · linarith only [h1, h2, h78, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h80 | h80
                · linarith only [h1, h62, h80, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h82, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                    · linarith only [h0, h2, h64, h82, h84, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                      · linarith only [h0, h76, h86, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                        · linarith only [h1, h64, h78, h88, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
                          · linarith only [h1, h80, h90, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                            · linarith only [h1, h2, h82, h84, h88, h92, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h2, h84, h92, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h95 | h95
      · rcases m.htr 0 1 5 (by decide) (by decide) with h96 | h96
        · linarith only [h96, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h98 | h98
          · linarith only [h0, h1, h98, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h100 | h100
            · linarith only [h0, h100, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h102 | h102
              · rcases m.htr 0 3 5 (by decide) (by decide) with h103 | h103
                · linarith only [h103, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h105 | h105
                  · linarith only [h1, h103, h105, h95, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
                    · linarith only [h0, h1, h103, h107, h98, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                      · linarith only [h0, h100, h109, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
                          · linarith only [h0, h1, h103, h107, h112, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h112, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h111, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h102, h95, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h117 | h117
        · linarith only [h117, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h119 | h119
          · linarith only [h0, h1, h119, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h121 | h121
            · linarith only [h0, h121, h95, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
              · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
                · linarith only [h124, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                  · linarith only [h123, h124, h126, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h128 | h128
                    · linarith only [h0, h119, h123, h124, h128, h95, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                      · linarith only [h0, h121, h130, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                          · linarith only [h0, h123, h124, h128, h133, h95, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h133, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h132, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h137 | h137
                · linarith only [h137, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h139 | h139
                  · linarith only [h139, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
                    · linarith only [h0, h141, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h143 | h143
                      · linarith only [h0, h1, h123, h139, h143, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                        · linarith only [h0, h1, h123, h141, h145, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h145, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h148 | h148
    · rcases m.htr 0 1 4 (by decide) (by decide) with h149 | h149
      · rcases m.htr 0 1 5 (by decide) (by decide) with h150 | h150
        · linarith only [h150, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h152 | h152
          · rcases m.htr 0 2 5 (by decide) (by decide) with h153 | h153
            · linarith only [h153, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h155 | h155
              · rcases m.htr 0 3 5 (by decide) (by decide) with h156 | h156
                · linarith only [h0, h148, h153, h156, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h158 | h158
                  · linarith only [h0, h148, h153, h155, h158, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                        · linarith only [h0, h148, h153, h162, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h0, h148, h153, h155, h162, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h165 | h165
                        · linarith only [h0, h148, h153, h165, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h0, h148, h153, h155, h165, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h152, h153, h160, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h169 | h169
                · linarith only [h149, h155, h169, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h171 | h171
                  · linarith only [h0, h149, h153, h171, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h175 | h175
                        · linarith only [h0, h148, h153, h155, h175, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h177 | h177
                          · linarith only [h148, h169, h177, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h179 | h179
                            · linarith only [h149, h155, h171, h179, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                              · linarith only [h148, h155, h173, h181, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                                · linarith only [h148, h173, h177, h183, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                                  · linarith only [h0, h149, h153, h173, h174, h175, h179, h181, h185, hc23, hc34, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                                    · linarith only [h0, h149, h153, h173, h174, h175, h179, h187, hc23, hc34, hlam, hphi]
                                    · rcases h5bigk with h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [hlam, p189_0]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h150, hlam, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h153, hlam, p189_0]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h169, hlam, p189_0]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h171, hlam, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h0, h149, h153, h173, h175, h177, hc23, hc35, hlam, hphi, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [hlam, p189_0]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h0, h149, h153, h173, h175, h177, h187, hc23, hc45, hlam, hphi, ht34, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h177, hlam, p189_0]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h179, hlam, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h0, h149, h153, h173, h174, h175, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h174, hlam, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [hlam, p189_0]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h183, hlam, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h185, hlam, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h0, h149, h153, h173, h175, h187, hc23, hc45, hlam, hphi, ht34, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h149, h150, h173, h175, h187, hc23, hc45, hlam, hphi, ht34, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h0, h149, h153, h173, h175, h187, hc23, hc45, hlam, hphi, ht34, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [hlam, p189_0]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h187, hlam, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h0, h149, h153, h173, h175, hc23, hc45, hlam, hphi, ht34, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h0, h149, h153, h173, h174, h175, hc23, hc45, hlam, hphi, ht34, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h0, h149, h153, h173, h175, hc23, hc45, hlam, hphi, ht34, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [h169, hc03, hc45, hlam, hphi, ht34, p189_1]
                                      · have p189_0 := h189c.1
                                        have p189_1 := h189c.2.1
                                        have p189_2 := h189c.2.2.1
                                        have p189_3 := h189c.2.2.2
                                        linarith only [hlam, p189_0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                        · linarith only [h148, h215, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h217 | h217
                          · linarith only [h0, h149, h153, h169, h174, h215, h217, hc02, hc25, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
                            · linarith only [h0, h149, h174, h219, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                              · linarith only [h152, h155, h221, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h223 | h223
                                · linarith only [h0, h149, h173, h174, h215, h217, h223, hlam]
                                · linarith only [h0, h149, h173, h174, h215, h223, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h148, h152, h153, h173, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
          · linarith only [h0, h148, h152, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h228 | h228
        · linarith only [h228, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h230 | h230
          · rcases m.htr 0 2 5 (by decide) (by decide) with h231 | h231
            · linarith only [h231, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h233 | h233
              · linarith only [h148, h149, h233, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h235 | h235
                · linarith only [h0, h148, h231, h235, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
                  · linarith only [h237, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                        · linarith only [h0, h148, h231, h233, h241, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h243 | h243
                          · linarith only [h148, h235, h243, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                            · linarith only [h148, h149, h237, h239, h241, h245, hc23, hc34, hlam, hphi]
                            · linarith only [h148, h149, h239, h245, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h248 | h248
                        · linarith only [h148, h248, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h250 | h250
                          · linarith only [h0, h148, h240, h250, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h252 | h252
                            · linarith only [h148, h149, h237, h239, h248, h252, hc23, hc34, hlam, hphi]
                            · linarith only [h148, h149, h239, h252, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h230, h231, h239, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
          · linarith only [h0, h148, h230, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h257 | h257
      · rcases m.htr 0 1 5 (by decide) (by decide) with h258 | h258
        · linarith only [h258, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h260 | h260
          · rcases m.htr 0 2 5 (by decide) (by decide) with h261 | h261
            · linarith only [h261, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h263 | h263
              · rcases m.htr 0 3 5 (by decide) (by decide) with h264 | h264
                · linarith only [h260, h261, h264, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h266 | h266
                  · linarith only [h148, h257, h260, h261, h266, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h269 | h269
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h270 | h270
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
                            · linarith only [h148, h257, h260, h261, h266, h272, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                              · linarith only [h260, h261, h274, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                              · linarith only [h260, h261, h263, h274, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                            · linarith only [h148, h257, h271, h277, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                              · linarith only [h260, h261, h279, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                              · linarith only [h260, h261, h263, h279, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                        · linarith only [h148, h257, h263, h270, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h283 | h283
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h284 | h284
                          · linarith only [h148, h257, h264, h268, h269, h283, h284, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h286 | h286
                            · linarith only [h257, h286, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h288 | h288
                              · linarith only [h260, h261, h288, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                              · linarith only [h148, h257, h283, h284, h288, hc23, hc35, hlam, hphi]
                        · linarith only [h148, h260, h261, h263, h283, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h257, h260, h261, h268, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
              · linarith only [h148, h257, h263, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h294 | h294
            · linarith only [h294, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h296 | h296
              · rcases m.htr 0 3 5 (by decide) (by decide) with h297 | h297
                · linarith only [h297, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
                  · linarith only [h257, h299, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h301 | h301
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h302 | h302
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h303 | h303
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h304 | h304
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                            · linarith only [h0, h257, h260, h297, h299, h301, h304, h305, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h307 | h307
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h308 | h308
                                · linarith only [h0, h260, h297, h301, h308, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h257, h260, h301, h303, h304, h308, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h257, h260, h303, h307, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h312 | h312
                            · linarith only [h257, h312, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h314 | h314
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h315 | h315
                                · linarith only [h301, h304, h315, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h317 | h317
                                  · linarith only [h302, h312, h314, h315, h317, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h319 | h319
                                    · linarith only [h0, h257, h260, h302, h303, h312, h315, h319, hlam]
                                    · linarith only [h0, h257, h260, h301, h303, h304, h319, hc34, hc45, hlam, hphi]
                              · linarith only [h0, h257, h260, h303, h314, hlam]
                        · linarith only [h0, h260, h296, h301, h303, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h257, h260, h301, h302, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h325 | h325
                      · linarith only [h0, h257, h294, h301, h325, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h327 | h327
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h328 | h328
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h329 | h329
                            · linarith only [h257, h329, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h331 | h331
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h332 | h332
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h333 | h333
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h334 | h334
                                    · linarith only [h0, h257, h260, h297, h327, h328, h329, h334, hlam]
                                    · rcases h5bigk with h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h258, hlam, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h294, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h297, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h299, hlam, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h329, h331, h333, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p336_1, u5ehi0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h325, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h0, h257, h260, h297, h327, h329, h331, h333, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h329, hlam, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        rcases p336_3 (m.d 0 5) (by simp) with h347 | h347
                                        · linarith only [h294, h347, hlam]
                                        · rcases p336_3 (m.d 1 5) (by simp) with h349 | h349
                                          · linarith only [h325, h349, hlam]
                                          · linarith only [h258, h349, hlam]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h0, h257, h325, h327, h331, h333, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h0, h257, h260, h297, h327, h331, h333, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h0, h257, h260, h297, h327, h328, h329, h331, h333, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h0, h257, h260, h297, h327, h328, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h328, hlam, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h332, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h334, hlam, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h0, h257, h260, h297, h327, hc34, hc45, hlam, hphi, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h257, h258, h327, hc34, hc45, hlam, hphi, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h333, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h0, h257, h260, h297, h327, h331, h333, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hlam, p336_0]
                                  · linarith only [h0, h257, h325, h327, h333, hc34, hc45, hlam, hphi]
                                · linarith only [h0, h257, h301, h327, h332, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h257, h260, h297, h301, h327, h328, h331, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h369 | h369
                            · linarith only [h257, h369, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h371 | h371
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h372 | h372
                                · linarith only [h0, h257, h301, h327, h328, h372, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h257, h301, h327, h372, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h257, h301, h327, h371, hlam]
                        · linarith only [h0, h257, h296, h297, h301, h327, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
              · linarith only [h0, h257, h260, h296, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h378 | h378
        · linarith only [h378, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h380 | h380
          · rcases m.htr 0 2 5 (by decide) (by decide) with h381 | h381
            · linarith only [h381, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h383 | h383
              · rcases m.htr 0 3 5 (by decide) (by decide) with h384 | h384
                · linarith only [h380, h381, h384, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h386 | h386
                  · linarith only [h380, h381, h383, h386, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h388 | h388
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h389 | h389
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
                              · linarith only [h380, h381, h393, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                              · linarith only [h380, h381, h383, h393, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
                              · linarith only [h380, h381, h396, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                              · linarith only [h380, h381, h383, h396, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
                            · linarith only [h257, h386, h390, h391, h399, hc01, hc35, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
                              · linarith only [h380, h401, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h383, h401, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h380, h381, h383, h390, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h405 | h405
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h406 | h406
                          · linarith only [h383, h384, h388, h389, h406, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                            · linarith only [h257, h386, h388, h389, h405, h408, hc01, hc25, hlam, hphi, ht12]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h410 | h410
                              · linarith only [h380, h381, h410, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                              · linarith only [h383, h410, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h380, h381, h383, h405, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h380, h381, h388, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h415 | h415
                · linarith only [h380, h381, h415, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h417 | h417
                  · linarith only [h417, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h420 | h420
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h421 | h421
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h422 | h422
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h423 | h423
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h424 | h424
                              · linarith only [h380, h383, h424, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h426 | h426
                                · linarith only [h148, h380, h381, h415, h426, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h428 | h428
                                  · linarith only [h257, h417, h419, h421, h424, h428, hc01, hc12, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h430 | h430
                                    · linarith only [h380, h381, h419, h421, h428, h430, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                    · linarith only [h148, h383, h419, h421, h423, h430, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h433 | h433
                              · linarith only [h148, h380, h383, h433, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h435 | h435
                                · linarith only [h380, h381, h420, h435, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h437 | h437
                                  · linarith only [h257, h380, h381, h419, h422, h423, h433, h435, h437, hc01, hc12, hc23, hc34, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h439 | h439
                                    · linarith only [h421, h423, h439, hlam]
                                    · rcases h5bigk with h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [hlam, p441_0]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h378, hlam, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h381, hlam, p441_0]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h415, hlam, p441_0]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h417, hlam, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h380, h381, h423, hc23, hc45, hlam, hphi, ht34, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [hlam, p441_0]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h380, h381, h423, hc23, hc45, hlam, hphi, ht34, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h380, h381, h423, h435, hc23, hc45, hlam, hphi, ht34, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h423, hlam, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h380, h381, h419, h422, h435, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h420, hlam, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [hlam, p441_0]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h435, hlam, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h437, hlam, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h380, h381, h419, h422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h422, hlam, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h419, h422, hc12, hlam, hphi, ht01, ht0b, ht5b, p441_1, u5ehi2]
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
                                        linarith only [h380, h381, hc23, hc45, hlam, hphi, ht34, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h378, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h380, h381, hc23, hc45, hlam, hphi, ht34, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [h380, h381, h435, hc23, hc45, hlam, hphi, ht34, p441_1]
                                      · have p441_0 := h441c.1
                                        have p441_1 := h441c.2.1
                                        have p441_2 := h441c.2.2.1
                                        have p441_3 := h441c.2.2.2
                                        linarith only [hlam, p441_0]
                          · linarith only [h148, h383, h421, h422, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h468 | h468
                          · linarith only [h148, h415, h421, h468, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h470 | h470
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h471 | h471
                              · linarith only [h380, h381, h421, h471, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h473 | h473
                                · linarith only [h380, h381, h468, h473, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h475 | h475
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h476 | h476
                                    · rcases h5bigk with h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [hlam, p477_0]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h378, hlam, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h381, hlam, p477_0]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h415, hlam, p477_0]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h417, hlam, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h380, h381, h468, hc23, hc35, hlam, hphi, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [hlam, p477_0]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h380, h381, h468, hc23, hc35, hlam, hphi, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h468, hlam, p477_0]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h383, h417, h421, h470, hc03, hc34, hlam, hphi, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h380, h381, h420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h420, hlam, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [hlam, p477_0]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h473, hlam, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h148, h383, h417, h420, hc01, hc12, hlam, hphi, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h380, h381, hc23, hc35, hlam, hphi, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h378, hc01, hc35, hlam, hphi, ht12, ht23, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h380, h381, hc23, hc35, hlam, hphi, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [hlam, p477_0]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h148, h383, h417, h476, hc01, hc34, hlam, hphi, ht12, ht23, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h380, h381, h475, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p477_1]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h470, hlam, p477_0]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h475, hlam, p477_0]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [h476, hlam, p477_0]
                                      · have p477_0 := h477c.1
                                        have p477_1 := h477c.2.1
                                        have p477_2 := h477c.2.2.1
                                        have p477_3 := h477c.2.2.2
                                        linarith only [hlam, p477_0]
                                    · linarith only [h421, h470, h476, hlam]
                                  · linarith only [h380, h381, h421, h470, h475, hc23, hc34, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
                              · linarith only [h380, h505, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h507 | h507
                                · linarith only [h380, h381, h420, h507, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h509 | h509
                                  · linarith only [h257, h470, h509, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h511 | h511
                                    · linarith only [h148, h421, h470, h511, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h148, h421, h511, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h514 | h514
                        · linarith only [h148, h383, h419, h420, h514, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h516 | h516
                          · linarith only [h148, h415, h419, h420, h516, hc01, hc25, hlam, hphi, ht12]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h518 | h518
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
                              · linarith only [h380, h514, h519, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h521 | h521
                                · linarith only [h380, h381, h516, h521, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h523 | h523
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h524 | h524
                                    · rcases h5bigk with h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h378, hlam, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h381, hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h415, hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h417, hlam, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h380, h381, h420, h521, hc23, hc35, hlam, hphi, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h420, hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h516, hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h148, h383, h417, h518, hc01, hc14, hlam, hphi, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h380, h381, h521, hc23, hc35, hlam, hphi, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h378, h521, hc01, hc35, hlam, hphi, ht12, ht23, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h521, hlam, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h148, h383, h417, h519, h523, hc01, hc34, hlam, hphi, ht12, ht23, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h380, h381, hc23, hc35, hlam, hphi, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h148, h383, h417, h518, hc01, hc35, hlam, hphi, ht12, ht23, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h380, h381, hc23, hc35, hlam, hphi, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h148, h383, h417, h524, hc01, hc34, hlam, hphi, ht12, ht23, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h380, h381, hc23, hc45, hlam, hphi, ht34, p525_1]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h518, hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h523, hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [h524, hlam, p525_0]
                                      · have p525_0 := h525c.1
                                        have p525_1 := h525c.2.1
                                        have p525_2 := h525c.2.2.1
                                        have p525_3 := h525c.2.2.2
                                        linarith only [hlam, p525_0]
                                    · linarith only [h514, h518, h524, hlam]
                                  · linarith only [h148, h419, h420, h514, h518, h523, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                              · linarith only [h380, h553, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h555 | h555
                                · linarith only [h380, h381, h555, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h557 | h557
                                  · linarith only [h257, h518, h557, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h559 | h559
                                    · linarith only [h148, h419, h420, h557, h559, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h148, h514, h559, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h380, h381, h419, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h563 | h563
            · linarith only [h563, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h565 | h565
              · rcases m.htr 0 3 5 (by decide) (by decide) with h566 | h566
                · linarith only [h566, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h568 | h568
                  · linarith only [h568, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h570 | h570
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h571 | h571
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h572 | h572
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h573 | h573
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h574 | h574
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h575 | h575
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
                                · linarith only [h565, h566, h570, h576, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h380, h570, h573, h576, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h380, h565, h575, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h580 | h580
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h581 | h581
                                · linarith only [h565, h566, h570, h581, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h380, h570, h573, h581, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h380, h565, h580, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h585 | h585
                            · linarith only [h257, h568, h572, h573, h585, hc01, hc35, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h587 | h587
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h588 | h588
                                · linarith only [h148, h573, h588, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h590 | h590
                                  · linarith only [h257, h585, h590, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h592 | h592
                                    · linarith only [h565, h585, h592, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi1]
                                    · rcases h5bigk with h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [hlam, p594_0]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h378, hlam, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h563, hlam, p594_0]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h566, hlam, p594_0]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h568, hlam, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h565, h566, h573, h592, hc34, hc45, hlam, hphi, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [hlam, p594_0]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h0, h380, h573, h588, h592, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h573, hlam, p594_0]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h585, hlam, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h565, h566, h571, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h571, hlam, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [hlam, p594_0]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h588, hlam, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h590, hlam, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h565, h566, h592, hc34, hc45, hlam, hphi, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h378, h592, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h0, h563, h592, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [hlam, p594_0]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h592, hlam, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h565, h566, hc34, hc45, hlam, hphi, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h0, h380, h570, h573, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h0, h380, h588, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [h565, h566, hc34, hc45, hlam, hphi, p594_1]
                                      · have p594_0 := h594c.1
                                        have p594_1 := h594c.2.1
                                        have p594_2 := h594c.2.2.1
                                        have p594_3 := h594c.2.2.2
                                        linarith only [hlam, p594_0]
                              · linarith only [h0, h380, h565, h587, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h148, h565, h572, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h380, h570, h571, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h623 | h623
                      · linarith only [h0, h563, h570, h623, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h625 | h625
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h626 | h626
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h627 | h627
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h628 | h628
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h629 | h629
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h630 | h630
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h631 | h631
                                    · linarith only [h257, h565, h568, h631, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                    · rcases h5bigk with h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h378, hlam, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h563, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h566, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h568, hlam, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        rcases p633_3 (m.d 0 5) (by simp) with h639 | h639
                                        · linarith only [h378, h639, hlam]
                                        · rcases p633_3 (m.d 1 5) (by simp) with h641 | h641
                                          · rcases p633_3 (m.d 2 5) (by simp) with h642 | h642
                                            · rcases p633_3 (m.d 3 5) (by simp) with h643 | h643
                                              · linarith only [h626, h643, hlam]
                                              · linarith only [h566, h643, hlam]
                                            · linarith only [h563, h642, hlam]
                                          · linarith only [h378, h641, hlam]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h623, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h565, h566, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h257, h568, h623, h628, h630, hc01, hc23, hlam, hphi, ht12, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        rcases p633_3 (m.d 0 5) (by simp) with h652 | h652
                                        · linarith only [h563, h652, hlam]
                                        · rcases p633_3 (m.d 1 5) (by simp) with h654 | h654
                                          · linarith only [h623, h654, hlam]
                                          · linarith only [h378, h654, hlam]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h378, h628, h630, hc01, hc23, hlam, hphi, ht12, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h565, h566, h628, h630, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h565, h566, h628, h630, h631, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h565, h566, h631, hc34, hc45, hlam, hphi, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h626, hlam, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h629, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h631, hlam, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h565, h566, hc34, hc45, hlam, hphi, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h627, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h630, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h565, h566, hc34, hc45, hlam, hphi, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [hlam, p633_0]
                                  · linarith only [h0, h570, h623, h625, h627, h630, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h257, h568, h570, h625, h627, h629, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h565, h566, h570, h626, h628, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h674 | h674
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h675 | h675
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h676 | h676
                                  · linarith only [h257, h627, h676, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h678 | h678
                                    · linarith only [h0, h565, h623, h676, h678, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                    · rcases h5bigk with h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [hlam, p680_0]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h378, hlam, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h563, hlam, p680_0]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h566, hlam, p680_0]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h568, hlam, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h565, h566, h623, h676, hc34, hc45, hlam, hphi, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [hlam, p680_0]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h623, hlam, p680_0]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h565, h566, h623, h676, hc34, hc45, hlam, hphi, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h627, hlam, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h565, h566, h676, hc34, hc45, hlam, hphi, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h378, h676, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [hlam, p680_0]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h565, h566, h676, hc34, hc45, hlam, hphi, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h676, hlam, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h565, h566, h623, h626, h676, hc34, hc45, hlam, hphi, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h626, hlam, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h675, hlam, p680_0]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [hlam, p680_0]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h678, hlam, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h565, h566, hc34, hc45, hlam, hphi, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h378, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h0, h563, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [h565, h566, hc34, hc45, hlam, hphi, p680_1]
                                      · have p680_0 := h680c.1
                                        have p680_1 := h680c.2.1
                                        have p680_2 := h680c.2.2.1
                                        have p680_3 := h680c.2.2.2
                                        linarith only [hlam, p680_0]
                                · linarith only [h0, h570, h675, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h565, h566, h570, h626, h674, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h708 | h708
                            · linarith only [h257, h568, h625, h626, h708, hc01, hc35, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h710 | h710
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h711 | h711
                                · linarith only [h148, h626, h711, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h570, h711, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h565, h570, h710, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h148, h565, h625, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h716 | h716
                · linarith only [h716, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h718 | h718
                  · linarith only [h718, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h720 | h720
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h721 | h721
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h722 | h722
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h723 | h723
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h724 | h724
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h725 | h725
                              · linarith only [h148, h565, h720, h725, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h380, h720, h722, h725, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h728 | h728
                              · linarith only [h0, h380, h565, h720, h728, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h380, h722, h724, h728, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h380, h565, h722, h723, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h732 | h732
                          · linarith only [h0, h380, h716, h722, h732, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h734 | h734
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h735 | h735
                              · linarith only [h148, h722, h735, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h737 | h737
                                · linarith only [h0, h380, h716, h720, h737, hc01, hc12, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h739 | h739
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h740 | h740
                                    · rcases h5bigk with h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [hlam, p741_0]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h378, hlam, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h563, hlam, p741_0]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h716, hlam, p741_0]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h718, hlam, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        rcases p741_3 (m.d 0 5) (by simp) with h747 | h747
                                        · linarith only [h378, h747, hlam]
                                        · rcases p741_3 (m.d 1 5) (by simp) with h749 | h749
                                          · rcases p741_3 (m.d 2 5) (by simp) with h750 | h750
                                            · linarith only [h721, h750, hlam]
                                            · linarith only [h563, h750, hlam]
                                          · linarith only [h378, h749, hlam]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [hlam, p741_0]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h0, h380, h734, h737, hc01, hc14, hlam, hphi, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h732, hlam, p741_0]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h0, h380, h565, h718, h722, h734, hc01, hc34, hlam, hphi, ht12, ht23, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h0, h380, h565, h718, h721, hc01, hc12, hlam, hphi, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h721, hlam, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [hlam, p741_0]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h737, hlam, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h0, h380, h565, h718, h721, hc01, hc12, hlam, hphi, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        rcases p741_3 (m.d 0 5) (by simp) with h763 | h763
                                        · linarith only [h716, h763, hlam]
                                        · rcases p741_3 (m.d 1 5) (by simp) with h765 | h765
                                          · linarith only [h732, h765, hlam]
                                          · linarith only [h378, h765, hlam]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h378, h740, hc01, hc34, hlam, hphi, ht12, ht23, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h0, h563, h740, hc01, hc34, hlam, hphi, ht12, ht23, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [hlam, p741_0]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h0, h380, h565, h718, h740, hc01, hc34, hlam, hphi, ht12, ht23, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h0, h380, h565, h718, h721, h739, hc01, hc12, hlam, hphi, p741_1]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h734, hlam, p741_0]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h739, hlam, p741_0]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [h740, hlam, p741_0]
                                      · have p741_0 := h741c.1
                                        have p741_1 := h741c.2.1
                                        have p741_2 := h741c.2.2.1
                                        have p741_3 := h741c.2.2.2
                                        linarith only [hlam, p741_0]
                                    · linarith only [h722, h734, h740, hlam]
                                  · linarith only [h0, h380, h722, h734, h735, h739, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h779 | h779
                              · linarith only [h0, h380, h565, h720, h779, hc01, hc12, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h781 | h781
                                · linarith only [h0, h380, h716, h720, h722, h734, h781, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h783 | h783
                                  · linarith only [h148, h722, h734, h783, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h785 | h785
                                    · linarith only [h0, h380, h720, h722, h734, h785, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h0, h380, h720, h722, h785, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h380, h720, h721, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h789 | h789
                      · linarith only [h0, h563, h720, h789, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h791 | h791
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h792 | h792
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h793 | h793
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h794 | h794
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h795 | h795
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h796 | h796
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h797 | h797
                                    · linarith only [h0, h380, h565, h718, h791, h797, hc01, hc13, hlam, hphi]
                                    · linarith only [h0, h380, h565, h793, h797, hc01, hc14, hlam, hphi]
                                  · linarith only [h0, h380, h565, h720, h791, h793, h794, h796, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h720, h792, h795, hlam]
                              · linarith only [h0, h380, h716, h720, h792, h794, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h803 | h803
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h804 | h804
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h805 | h805
                                  · linarith only [h257, h793, h805, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h807 | h807
                                    · linarith only [h791, h793, h807, hlam]
                                    · rcases h5bigk with h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c | h809c
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [hlam, p809_0]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h378, hlam, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h563, hlam, p809_0]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h716, hlam, p809_0]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h718, hlam, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        rcases p809_3 (m.d 0 5) (by simp) with h815 | h815
                                        · linarith only [h378, h815, hlam]
                                        · rcases p809_3 (m.d 1 5) (by simp) with h817 | h817
                                          · rcases p809_3 (m.d 2 5) (by simp) with h818 | h818
                                            · rcases p809_3 (m.d 3 5) (by simp) with h819 | h819
                                              · linarith only [h792, h819, hlam]
                                              · linarith only [h716, h819, hlam]
                                            · linarith only [h563, h818, hlam]
                                          · linarith only [h378, h817, hlam]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [hlam, p809_0]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h789, hlam, p809_0]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h0, h380, h565, h792, h807, hc01, hc13, hlam, hphi, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h793, hlam, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        rcases p809_3 (m.d 0 5) (by simp) with h828 | h828
                                        · linarith only [h563, h828, hlam]
                                        · rcases p809_3 (m.d 1 5) (by simp) with h830 | h830
                                          · linarith only [h789, h830, hlam]
                                          · linarith only [h378, h830, hlam]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h378, h805, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [hlam, p809_0]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h0, h380, h565, h805, h807, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h805, hlam, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h0, h380, h565, h718, h720, h792, hc01, hc23, hlam, hphi, ht12, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h792, hlam, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h804, hlam, p809_0]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [hlam, p809_0]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h807, hlam, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        rcases p809_3 (m.d 0 5) (by simp) with h842 | h842
                                        · linarith only [h718, h842, hlam]
                                        · rcases p809_3 (m.d 1 5) (by simp) with h844 | h844
                                          · linarith only [h793, h844, hlam]
                                          · linarith only [h378, h844, hlam]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h378, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h0, h563, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [h0, h380, h716, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p809_1]
                                      · have p809_0 := h809c.1
                                        have p809_1 := h809c.2.1
                                        have p809_2 := h809c.2.2.1
                                        have p809_3 := h809c.2.2.2
                                        linarith only [hlam, p809_0]
                                · linarith only [h0, h720, h804, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h720, h791, h803, hlam]
                          · linarith only [h0, h380, h565, h791, h792, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h854 | h854
                          · linarith only [h0, h380, h716, h791, h854, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h856 | h856
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h857 | h857
                              · linarith only [h148, h791, h857, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h720, h857, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h860 | h860
                              · linarith only [h0, h720, h791, h860, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h720, h860, hc01, hc34, hlam, hphi, ht12, ht23]

theorem n7l_sBT2_H_R_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h2bigk := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h15, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · linarith only [h0, h12, h14, h15, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                                · linarith only [h0, h14, h18, h2, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                                  · linarith only [h0, h20, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                                    · linarith only [h0, h11, h14, h20, h22, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                    · linarith only [h0, h11, h13, h14, h22, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                                · linarith only [h0, h26, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · linarith only [h0, h12, h25, h26, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                                · linarith only [h0, h2, h25, h29, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                                  · linarith only [h11, h13, h25, h31, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
                                    · linarith only [h11, h13, h33, hlam]
                                    · rcases h2bigk with h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, p35_1, u5ehi2]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h11, h13, h2, h25, h5, h7, hlam, p35_2]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        rcases p35_3 (m.d 0 2) (by simp) with h39 | h39
                                        · rcases p35_3 (m.d 1 2) (by simp) with h40 | h40
                                          · linarith only [h0, h40, hlam]
                                          · linarith only [h40, h9, hlam]
                                        · linarith only [h39, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        rcases p35_3 (m.d 0 2) (by simp) with h44 | h44
                                        · rcases p35_3 (m.d 1 2) (by simp) with h45 | h45
                                          · linarith only [h0, h45, hlam]
                                          · linarith only [h10, h45, hlam]
                                        · linarith only [h44, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h0, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        rcases p35_3 (m.d 0 2) (by simp) with h51 | h51
                                        · rcases p35_3 (m.d 1 2) (by simp) with h52 | h52
                                          · rcases p35_3 (m.d 2 3) (by simp) with h53 | h53
                                            · linarith only [h53, hlam, p35_0]
                                            · rcases p35_3 (m.d 2 4) (by simp) with h55 | h55
                                              · linarith only [h55, h9, hlam]
                                              · linarith only [h25, h55, hlam]
                                          · linarith only [h52, hlam, p35_0]
                                        · linarith only [h2, h51, hlam]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        rcases p35_3 (m.d 0 2) (by simp) with h60 | h60
                                        · rcases p35_3 (m.d 1 2) (by simp) with h61 | h61
                                          · rcases p35_3 (m.d 2 3) (by simp) with h62 | h62
                                            · linarith only [h62, h8, hlam]
                                            · rcases p35_3 (m.d 2 4) (by simp) with h64 | h64
                                              · linarith only [h64, hlam, p35_0]
                                              · rcases p35_3 (m.d 2 5) (by simp) with h66 | h66
                                                · linarith only [h10, h66, hlam]
                                                · linarith only [h31, h66, hlam]
                                          · linarith only [h61, hlam, p35_0]
                                        · linarith only [h3, h60, hlam]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p35_1, u5ehi2]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h2, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h8, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h25, hlam, p35_1]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h29, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h3, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h9, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p35_1]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h31, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h4, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h10, hlam, p35_0]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p35_1]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [h1, h12, h29, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p35_1]
                                      · have p35_0 := h35c.1
                                        have p35_1 := h35c.2.1
                                        have p35_2 := h35c.2.2.1
                                        have p35_3 := h35c.2.2.2
                                        linarith only [hlam, p35_0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                            · linarith only [h0, h11, h12, h2, h6, h87, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                                · linarith only [h12, h8, h90, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                                  · linarith only [h0, h87, h9, h92, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                                    · linarith only [h0, h2, h87, h89, h94, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases h2bigk with h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, p96_1, u5ehi2]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        rcases p96_3 (m.d 0 2) (by simp) with h99 | h99
                                        · rcases p96_3 (m.d 1 2) (by simp) with h100 | h100
                                          · linarith only [h0, h100, hlam]
                                          · linarith only [h100, h8, hlam]
                                        · linarith only [h99, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        rcases p96_3 (m.d 0 2) (by simp) with h104 | h104
                                        · rcases p96_3 (m.d 1 2) (by simp) with h105 | h105
                                          · linarith only [h0, h105, hlam]
                                          · linarith only [h105, h9, hlam]
                                        · linarith only [h104, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        rcases p96_3 (m.d 0 2) (by simp) with h109 | h109
                                        · rcases p96_3 (m.d 1 2) (by simp) with h110 | h110
                                          · linarith only [h0, h110, hlam]
                                          · linarith only [h10, h110, hlam]
                                        · linarith only [h109, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h0, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h0, h89, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p96_1]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        rcases p96_3 (m.d 0 2) (by simp) with h117 | h117
                                        · rcases p96_3 (m.d 1 2) (by simp) with h118 | h118
                                          · rcases p96_3 (m.d 2 3) (by simp) with h119 | h119
                                            · linarith only [h119, h8, hlam]
                                            · linarith only [h119, h89, hlam]
                                          · linarith only [h118, hlam, p96_0]
                                        · linarith only [h117, h3, hlam]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h0, h89, h90, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p96_1]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h2, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h8, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h0, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p96_1]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h90, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h3, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h9, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h89, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h92, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h4, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h10, hlam, p96_0]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p96_1]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [h0, h10, h89, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p96_1]
                                      · have p96_0 := h96c.1
                                        have p96_1 := h96c.2.1
                                        have p96_2 := h96c.2.2.1
                                        have p96_3 := h96c.2.2.2
                                        linarith only [hlam, p96_0]
                              · linarith only [h11, h12, h89, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h141 | h141
                          · linarith only [h0, h11, h141, h2, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                              · linarith only [h0, h11, h144, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                                · linarith only [h0, h10, h141, h146, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h148 | h148
                                  · linarith only [h0, h148, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h150 | h150
                                    · rcases h2bigk with h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h0, h143, h144, h148, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p151_1]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h11, h143, h144, h148, h2, h5, hlam, p151_2]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h11, h143, h148, h2, h5, hlam, p151_2]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        rcases p151_3 (m.d 0 2) (by simp) with h156 | h156
                                        · rcases p151_3 (m.d 1 2) (by simp) with h157 | h157
                                          · linarith only [h0, h157, hlam]
                                          · linarith only [h10, h157, hlam]
                                        · linarith only [h156, hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h0, hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        rcases p151_3 (m.d 0 2) (by simp) with h163 | h163
                                        · rcases p151_3 (m.d 1 2) (by simp) with h164 | h164
                                          · rcases p151_3 (m.d 2 3) (by simp) with h165 | h165
                                            · linarith only [h165, hlam, p151_0]
                                            · rcases p151_3 (m.d 2 4) (by simp) with h167 | h167
                                              · linarith only [h167, h9, hlam]
                                              · linarith only [h144, h167, hlam]
                                          · linarith only [h164, hlam, p151_0]
                                        · linarith only [h163, h2, hlam]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        rcases p151_3 (m.d 0 2) (by simp) with h172 | h172
                                        · rcases p151_3 (m.d 1 2) (by simp) with h173 | h173
                                          · rcases p151_3 (m.d 2 3) (by simp) with h174 | h174
                                            · linarith only [h174, h8, hlam]
                                            · rcases p151_3 (m.d 2 4) (by simp) with h176 | h176
                                              · linarith only [h176, hlam, p151_0]
                                              · rcases p151_3 (m.d 2 5) (by simp) with h178 | h178
                                                · linarith only [h10, h178, hlam]
                                                · linarith only [h148, h178, hlam]
                                          · linarith only [h173, hlam, p151_0]
                                        · linarith only [h172, h3, hlam]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p151_1, u5ehi2]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h2, hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h8, hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h144, hlam, p151_1]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h146, hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h3, hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h9, hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h0, h11, h143, h148, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p151_1]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h148, hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h4, hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h10, hlam, p151_0]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p151_1]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [h0, h11, h143, h148, h2, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p151_1]
                                      · have p151_0 := h151c.1
                                        have p151_1 := h151c.2.1
                                        have p151_2 := h151c.2.2.1
                                        have p151_3 := h151c.2.2.2
                                        linarith only [hlam, p151_0]
                                    · linarith only [h11, h143, h150, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                              · linarith only [h0, h11, h200, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                                · linarith only [h0, h141, h202, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                                  · linarith only [h0, h11, h143, h204, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                                    · rcases h2bigk with h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, p207_1, u5ehi2]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h11, h143, h2, h206, h5, h8, hlam, p207_2]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h143, h2, h206, h5, h9, hlam, p207_2]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        rcases p207_3 (m.d 0 2) (by simp) with h212 | h212
                                        · rcases p207_3 (m.d 1 2) (by simp) with h213 | h213
                                          · linarith only [h0, h213, hlam]
                                          · linarith only [h10, h213, hlam]
                                        · linarith only [h212, hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h0, hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        rcases p207_3 (m.d 0 2) (by simp) with h219 | h219
                                        · rcases p207_3 (m.d 1 2) (by simp) with h220 | h220
                                          · rcases p207_3 (m.d 2 3) (by simp) with h221 | h221
                                            · linarith only [h221, hlam, p207_0]
                                            · rcases p207_3 (m.d 2 4) (by simp) with h223 | h223
                                              · linarith only [h223, h9, hlam]
                                              · linarith only [h200, h223, hlam]
                                          · linarith only [h220, hlam, p207_0]
                                        · linarith only [h2, h219, hlam]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        rcases p207_3 (m.d 0 2) (by simp) with h228 | h228
                                        · rcases p207_3 (m.d 1 2) (by simp) with h229 | h229
                                          · rcases p207_3 (m.d 2 3) (by simp) with h230 | h230
                                            · linarith only [h230, h8, hlam]
                                            · rcases p207_3 (m.d 2 4) (by simp) with h232 | h232
                                              · linarith only [h232, hlam, p207_0]
                                              · rcases p207_3 (m.d 2 5) (by simp) with h234 | h234
                                                · linarith only [h10, h234, hlam]
                                                · linarith only [h204, h234, hlam]
                                          · linarith only [h229, hlam, p207_0]
                                        · linarith only [h228, h3, hlam]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p207_1, u5ehi2]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h2, hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h8, hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h200, hlam, p207_1]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h202, hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h3, hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h9, hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h143, h2, h206, h5, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p207_1]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h204, hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h4, hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h10, hlam, p207_0]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p207_1]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [h0, h10, h143, h2, h206, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p207_1]
                                      · have p207_0 := h207c.1
                                        have p207_1 := h207c.2.1
                                        have p207_2 := h207c.2.2.1
                                        have p207_3 := h207c.2.2.2
                                        linarith only [hlam, p207_0]
                                    · rcases h2bigk with h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, p255_1, u5ehi2]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h11, h2, h206, h5, h7, h8, hlam, p255_2]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        rcases p255_3 (m.d 0 2) (by simp) with h259 | h259
                                        · rcases p255_3 (m.d 1 2) (by simp) with h260 | h260
                                          · linarith only [h0, h260, hlam]
                                          · linarith only [h260, h9, hlam]
                                        · linarith only [h259, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        rcases p255_3 (m.d 0 2) (by simp) with h264 | h264
                                        · rcases p255_3 (m.d 1 2) (by simp) with h265 | h265
                                          · linarith only [h0, h265, hlam]
                                          · linarith only [h10, h265, hlam]
                                        · linarith only [h264, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h0, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        rcases p255_3 (m.d 0 2) (by simp) with h271 | h271
                                        · rcases p255_3 (m.d 1 2) (by simp) with h272 | h272
                                          · rcases p255_3 (m.d 2 3) (by simp) with h273 | h273
                                            · linarith only [h273, hlam, p255_0]
                                            · rcases p255_3 (m.d 2 4) (by simp) with h275 | h275
                                              · linarith only [h275, h9, hlam]
                                              · linarith only [h200, h275, hlam]
                                          · linarith only [h272, hlam, p255_0]
                                        · linarith only [h2, h271, hlam]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        rcases p255_3 (m.d 0 2) (by simp) with h280 | h280
                                        · rcases p255_3 (m.d 1 2) (by simp) with h281 | h281
                                          · rcases p255_3 (m.d 2 3) (by simp) with h282 | h282
                                            · linarith only [h282, h8, hlam]
                                            · rcases p255_3 (m.d 2 4) (by simp) with h284 | h284
                                              · linarith only [h284, hlam, p255_0]
                                              · rcases p255_3 (m.d 2 5) (by simp) with h286 | h286
                                                · linarith only [h10, h286, hlam]
                                                · linarith only [h204, h286, hlam]
                                          · linarith only [h281, hlam, p255_0]
                                        · linarith only [h280, h3, hlam]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p255_1, u5ehi2]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h2, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h8, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h200, hlam, p255_1]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h202, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h3, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h9, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h204, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h4, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h10, hlam, p255_0]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p255_1]
                                      · have p255_0 := h255c.1
                                        have p255_1 := h255c.2.1
                                        have p255_2 := h255c.2.2.1
                                        have p255_3 := h255c.2.2.2
                                        linarith only [hlam, p255_0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h308 | h308
                          · linarith only [h0, h10, h308, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h310 | h310
                            · linarith only [h0, h10, h307, h310, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h312 | h312
                              · linarith only [h0, h10, h312, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h0, h10, h307, h312, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h315 | h315
                          · linarith only [h0, h10, h307, h315, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h317 | h317
                            · linarith only [h0, h10, h317, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
                              · linarith only [h0, h10, h307, h319, h4, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h321 | h321
                                · linarith only [h0, h10, h315, h321, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h323 | h323
                                  · linarith only [h0, h10, h2, h321, h323, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h325 | h325
                                    · linarith only [h10, h319, h323, h325, h9, hc23, hc34, hlam, hphi]
                                    · rcases h2bigk with h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        rcases p327_3 (m.d 0 2) (by simp) with h329 | h329
                                        · rcases p327_3 (m.d 1 2) (by simp) with h330 | h330
                                          · linarith only [h0, h330, hlam]
                                          · rcases p327_3 (m.d 2 3) (by simp) with h332 | h332
                                            · linarith only [h2, h332, hlam]
                                            · rcases p327_3 (m.d 2 4) (by simp) with h334 | h334
                                              · linarith only [h3, h334, hlam]
                                              · rcases p327_3 (m.d 2 5) (by simp) with h336 | h336
                                                · linarith only [h336, h4, hlam]
                                                · linarith only [h10, h336, hlam]
                                        · linarith only [h0, h329, hlam]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h10, h2, h319, h321, h325, h5, h7, h9, hlam, p327_2]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h10, h2, h321, h325, h5, h7, h9, hlam, p327_2]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h0, h10, h319, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h0, hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h10, h321, hc23, hc35, hlam, hphi, p327_1]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h0, h10, h319, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h10, hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h2, hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h8, hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h319, hlam, p327_1]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h321, hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h3, hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h9, hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h0, h10, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h323, hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h4, hlam, p327_0]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        rcases p327_3 (m.d 0 2) (by simp) with h360 | h360
                                        · rcases p327_3 (m.d 1 2) (by simp) with h361 | h361
                                          · linarith only [h10, h361, hlam]
                                          · linarith only [h361, h8, hlam]
                                        · linarith only [h2, h360, hlam]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        rcases p327_3 (m.d 0 2) (by simp) with h365 | h365
                                        · rcases p327_3 (m.d 1 2) (by simp) with h366 | h366
                                          · linarith only [h10, h366, hlam]
                                          · linarith only [h366, h9, hlam]
                                        · linarith only [h3, h365, hlam]
                                      · have p327_0 := h327c.1
                                        have p327_1 := h327c.2.1
                                        have p327_2 := h327c.2.2.1
                                        have p327_3 := h327c.2.2.2
                                        linarith only [hlam, p327_0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                      · linarith only [h0, h3, h371, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
                        · linarith only [h373, h8, h9, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h375 | h375
                          · linarith only [h0, h3, h375, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h377 | h377
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h378 | h378
                              · linarith only [h0, h3, h373, h378, h8, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h380 | h380
                                · linarith only [h371, h375, h380, h8, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h382 | h382
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h383 | h383
                                    · rcases h2bigk with h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        rcases p384_3 (m.d 0 2) (by simp) with h386 | h386
                                        · rcases p384_3 (m.d 1 2) (by simp) with h387 | h387
                                          · linarith only [h0, h387, hlam]
                                          · rcases p384_3 (m.d 2 3) (by simp) with h389 | h389
                                            · linarith only [h2, h389, hlam]
                                            · rcases p384_3 (m.d 2 4) (by simp) with h391 | h391
                                              · linarith only [h3, h391, hlam]
                                              · linarith only [h391, h9, hlam]
                                        · linarith only [h0, h386, hlam]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h2, h371, h378, h382, h5, h8, hlam, p384_2]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h0, h371, h382, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p384_1]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h0, h371, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p384_1]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h0, hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h371, h380, hc23, hc35, hlam, hphi, p384_1]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h9, hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h371, hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h2, hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h8, hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h378, hlam, p384_1]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h380, hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h3, hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h0, h3, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p384_1]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        rcases p384_3 (m.d 0 2) (by simp) with h410 | h410
                                        · rcases p384_3 (m.d 1 2) (by simp) with h411 | h411
                                          · linarith only [h411, h9, hlam]
                                          · linarith only [h411, h8, hlam]
                                        · linarith only [h2, h410, hlam]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h0, h2, h378, h5, hc01, hlam, hphi, ht0b, ht5b, p384_1, u5ehi2]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h4, hlam, p384_0]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p384_1]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        rcases p384_3 (m.d 0 2) (by simp) with h419 | h419
                                        · rcases p384_3 (m.d 1 2) (by simp) with h420 | h420
                                          · linarith only [h371, h420, hlam]
                                          · linarith only [h420, h8, hlam]
                                        · linarith only [h2, h419, hlam]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [h382, hlam, p384_1]
                                      · have p384_0 := h384c.1
                                        have p384_1 := h384c.2.1
                                        have p384_2 := h384c.2.2.1
                                        have p384_3 := h384c.2.2.2
                                        linarith only [hlam, p384_0]
                                    · linarith only [h0, h2, h378, h383, h5, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h377, h382, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h428 | h428
                              · linarith only [h0, h3, h428, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h430 | h430
                                · linarith only [h0, h2, h377, h430, h5, h7, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h432 | h432
                                  · linarith only [h0, h2, h377, h428, h432, h5, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h0, h2, h432, h5, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h435 | h435
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h436 | h436
                      · linarith only [h0, h2, h436, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h438 | h438
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h439 | h439
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h440 | h440
                            · linarith only [h0, h2, h435, h440, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h442 | h442
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h443 | h443
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h444 | h444
                                  · linarith only [h0, h2, h435, h436, h440, h443, h444, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h446 | h446
                                    · linarith only [h435, h436, h442, h444, h446, hlam]
                                    · rcases h2bigk with h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        rcases p448_3 (m.d 0 2) (by simp) with h450 | h450
                                        · rcases p448_3 (m.d 1 2) (by simp) with h451 | h451
                                          · linarith only [h0, h451, hlam]
                                          · rcases p448_3 (m.d 2 3) (by simp) with h453 | h453
                                            · linarith only [h2, h453, hlam]
                                            · linarith only [h453, h8, hlam]
                                        · linarith only [h0, h450, hlam]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h0, h435, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p448_1]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h2, h435, h8, hlam, p448_2]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h0, h435, h436, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p448_1]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h0, hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h8, hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h0, h4, h436, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p448_1]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h436, hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h2, hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h0, h2, h435, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p448_1]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        rcases p448_3 (m.d 0 2) (by simp) with h468 | h468
                                        · rcases p448_3 (m.d 1 2) (by simp) with h469 | h469
                                          · linarith only [h469, h8, hlam]
                                          · linarith only [h435, h469, hlam]
                                        · linarith only [h3, h468, hlam]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p448_1, u5ehi2]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h3, hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h435, hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h442, hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h444, hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h4, hlam, p448_0]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h0, h4, h435, h442, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p448_1]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [h443, hlam, p448_1]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        rcases p448_3 (m.d 0 2) (by simp) with h482 | h482
                                        · rcases p448_3 (m.d 1 2) (by simp) with h483 | h483
                                          · linarith only [h436, h483, hlam]
                                          · linarith only [h435, h483, hlam]
                                        · linarith only [h3, h482, hlam]
                                      · have p448_0 := h448c.1
                                        have p448_1 := h448c.2.1
                                        have p448_2 := h448c.2.2.1
                                        have p448_3 := h448c.2.2.2
                                        linarith only [hlam, p448_0]
                                · linarith only [h435, h439, h442, h443, h8, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h2, h435, h442, h5, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h490 | h490
                            · linarith only [h0, h2, h435, h490, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h493 | h493
                                · linarith only [h0, h2, h435, h439, h492, h493, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h2, h435, h492, h493, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h0, h2, h435, h492, h5, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h435, h438, h8, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h498 | h498
                      · linarith only [h0, h3, h435, h498, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h500 | h500
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h501 | h501
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h502 | h502
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h503 | h503
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h504 | h504
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h505 | h505
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h506 | h506
                                    · linarith only [h1, h500, h506, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · rcases h2bigk with h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        rcases p508_3 (m.d 0 2) (by simp) with h510 | h510
                                        · rcases p508_3 (m.d 1 2) (by simp) with h511 | h511
                                          · linarith only [h0, h511, hlam]
                                          · rcases p508_3 (m.d 2 3) (by simp) with h513 | h513
                                            · linarith only [h2, h513, hlam]
                                            · linarith only [h513, h8, hlam]
                                        · linarith only [h0, h510, hlam]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h0, h500, h502, h506, h8, hc01, hlam, hphi, ht0b, ht5b, p508_1, u5ehi3]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h0, h435, h502, h506, hc01, hlam, hphi, ht0b, ht5b, p508_1, u5ehi3]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        rcases p508_3 (m.d 0 2) (by simp) with h519 | h519
                                        · rcases p508_3 (m.d 1 2) (by simp) with h520 | h520
                                          · linarith only [h0, h520, hlam]
                                          · rcases p508_3 (m.d 2 3) (by simp) with h522 | h522
                                            · linarith only [h2, h522, hlam]
                                            · linarith only [h504, h522, hlam]
                                        · linarith only [h519, hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h0, hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h8, hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h435, hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h498, hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h2, hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        rcases p508_3 (m.d 0 2) (by simp) with h532 | h532
                                        · rcases p508_3 (m.d 1 2) (by simp) with h533 | h533
                                          · linarith only [h533, hlam, p508_0]
                                          · rcases p508_3 (m.d 2 3) (by simp) with h535 | h535
                                            · rcases p508_3 (m.d 2 4) (by simp) with h536 | h536
                                              · linarith only [h503, h536, hlam]
                                              · linarith only [h435, h536, hlam]
                                            · linarith only [h535, hlam, p508_0]
                                        · linarith only [h0, h532, hlam]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h435, h502, h506, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p508_1, u5ehi3]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h0, h2, h498, hc01, hlam, hphi, ht0b, ht5b, p508_1, u5ehi1]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h3, hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        rcases p508_3 (m.d 0 2) (by simp) with h545 | h545
                                        · rcases p508_3 (m.d 1 2) (by simp) with h546 | h546
                                          · linarith only [h546, hlam, p508_0]
                                          · rcases p508_3 (m.d 2 3) (by simp) with h548 | h548
                                            · rcases p508_3 (m.d 2 4) (by simp) with h549 | h549
                                              · rcases p508_3 (m.d 2 5) (by simp) with h550 | h550
                                                · linarith only [h505, h550, hlam]
                                                · linarith only [h498, h550, hlam]
                                              · linarith only [h549, hlam, p508_0]
                                            · linarith only [h548, h8, hlam]
                                        · linarith only [h0, h545, hlam]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h503, hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h498, hc12, hc24, hlam, hphi, p508_1]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h4, hlam, p508_0]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        rcases p508_3 (m.d 0 2) (by simp) with h560 | h560
                                        · rcases p508_3 (m.d 1 2) (by simp) with h561 | h561
                                          · linarith only [h561, hlam, p508_0]
                                          · rcases p508_3 (m.d 2 3) (by simp) with h563 | h563
                                            · rcases p508_3 (m.d 2 4) (by simp) with h564 | h564
                                              · rcases p508_3 (m.d 2 5) (by simp) with h565 | h565
                                                · rcases h5bigk with h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [hlam, p566_0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    rcases p566_3 (m.d 0 5) (by simp) with h568 | h568
                                                    · rcases p566_3 (m.d 1 5) (by simp) with h569 | h569
                                                      · linarith only [h569, hlam, p566_0]
                                                      · rcases p566_3 (m.d 2 5) (by simp) with h571 | h571
                                                        · linarith only [h4, h571, hlam]
                                                        · linarith only [h498, h571, hlam]
                                                    · linarith only [h568, hlam, p566_0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h0, h2, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p508_1, p566_1]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    rcases p566_3 (m.d 0 5) (by simp) with h576 | h576
                                                    · rcases p566_3 (m.d 1 5) (by simp) with h577 | h577
                                                      · linarith only [h0, h4, h498, h577, hc01, hlam, hphi, u0ehi4]
                                                      · linarith only [h501, h577, hlam]
                                                    · linarith only [h576, h6, hlam]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    rcases p566_3 (m.d 0 5) (by simp) with h581 | h581
                                                    · rcases p566_3 (m.d 1 5) (by simp) with h582 | h582
                                                      · linarith only [h1, h500, h502, h506, h582, hc01, hlam, hphi, ht0b, ht5b, p566_1, u5ehi3]
                                                      · linarith only [h502, h582, hlam]
                                                    · linarith only [h581, h7, hlam]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h0, h2, h500, h502, h8, hc01, hlam, hphi, ht0b, ht5b, p566_1, u5ehi0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [hlam, p566_0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h498, hlam, p566_0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h0, h2, h500, h502, h8, hc01, hlam, hphi, ht0b, ht5b, p566_1, u5ehi3]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h0, h2, h500, h502, h506, h8, hc01, hlam, hphi, ht0b, ht5b, p566_1, u5ehi3]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h4, hlam, p566_1]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h0, h2, h503, h505, hc01, hlam, hphi, ht0b, ht5b, p566_1, u5ehi1]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [hlam, p566_0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h0, h2, h503, h505, hc01, hlam, hphi, ht0b, ht5b, p566_1, u5ehi3]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h0, h2, h503, h505, h506, hc01, hlam, hphi, ht0b, ht5b, p566_1, u5ehi3]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h6, hlam, p566_1]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h501, hlam, p566_1]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h504, hlam, p566_0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [hlam, p566_0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h506, hlam, p566_1]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h7, hlam, p566_0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h502, hlam, p566_0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h505, hlam, p566_0]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [h0, h2, h5, h7, hc01, hlam, hphi, ht0b, ht5b, p566_1, u5ehi3]
                                                  · have p566_0 := h566c.1
                                                    have p566_1 := h566c.2.1
                                                    have p566_2 := h566c.2.2.1
                                                    have p566_3 := h566c.2.2.2
                                                    linarith only [hlam, p566_0]
                                                · linarith only [h565, hlam, p508_0]
                                              · linarith only [h435, h564, hlam]
                                            · linarith only [h563, h8, hlam]
                                        · linarith only [h0, h560, hlam]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h504, hlam, p508_1]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [h505, hlam, p508_1]
                                      · have p508_0 := h508c.1
                                        have p508_1 := h508c.2.1
                                        have p508_2 := h508c.2.2.1
                                        have p508_3 := h508c.2.2.2
                                        linarith only [hlam, p508_0]
                                  · linarith only [h0, h2, h435, h500, h502, h505, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h0, h2, h500, h502, h504, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h0, h2, h5, h500, h502, h503, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h616 | h616
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h617 | h617
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h618 | h618
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h619 | h619
                                    · linarith only [h500, h502, h619, hlam]
                                    · rcases h2bigk with h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h2, h435, h502, h616, h618, hlam, p621_2]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h0, h502, h616, h618, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p621_1]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h0, h500, h502, h618, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p621_1]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        rcases p621_3 (m.d 0 2) (by simp) with h626 | h626
                                        · rcases p621_3 (m.d 1 2) (by simp) with h627 | h627
                                          · linarith only [h0, h627, hlam]
                                          · rcases p621_3 (m.d 2 3) (by simp) with h629 | h629
                                            · linarith only [h2, h629, hlam]
                                            · linarith only [h617, h629, hlam]
                                        · linarith only [h626, hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h0, hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h8, hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h435, hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h498, hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h2, hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        rcases p621_3 (m.d 0 2) (by simp) with h639 | h639
                                        · rcases p621_3 (m.d 1 2) (by simp) with h640 | h640
                                          · linarith only [h640, hlam, p621_0]
                                          · rcases p621_3 (m.d 2 3) (by simp) with h642 | h642
                                            · rcases p621_3 (m.d 2 4) (by simp) with h643 | h643
                                              · linarith only [h616, h643, hlam]
                                              · linarith only [h435, h643, hlam]
                                            · linarith only [h642, hlam, p621_0]
                                        · linarith only [h0, h639, hlam]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h435, h502, h618, hc12, hc23, hlam, hphi, p621_1]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p621_1, u5ehi2]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h3, hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        rcases p621_3 (m.d 0 2) (by simp) with h652 | h652
                                        · rcases p621_3 (m.d 1 2) (by simp) with h653 | h653
                                          · linarith only [h653, hlam, p621_0]
                                          · rcases p621_3 (m.d 2 3) (by simp) with h655 | h655
                                            · rcases p621_3 (m.d 2 4) (by simp) with h656 | h656
                                              · rcases p621_3 (m.d 2 5) (by simp) with h657 | h657
                                                · linarith only [h618, h657, hlam]
                                                · linarith only [h498, h657, hlam]
                                              · linarith only [h656, hlam, p621_0]
                                            · linarith only [h655, h8, hlam]
                                        · linarith only [h0, h652, hlam]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h616, hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h435, h502, h618, hc12, hc24, hlam, hphi, p621_1]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h4, hlam, p621_0]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        rcases p621_3 (m.d 0 2) (by simp) with h667 | h667
                                        · rcases p621_3 (m.d 1 2) (by simp) with h668 | h668
                                          · linarith only [h668, hlam, p621_0]
                                          · rcases p621_3 (m.d 2 3) (by simp) with h670 | h670
                                            · rcases p621_3 (m.d 2 4) (by simp) with h671 | h671
                                              · rcases p621_3 (m.d 2 5) (by simp) with h672 | h672
                                                · rcases h5bigk with h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [hlam, p673_0]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    rcases p673_3 (m.d 0 5) (by simp) with h675 | h675
                                                    · rcases p673_3 (m.d 1 5) (by simp) with h676 | h676
                                                      · linarith only [h676, hlam, p673_0]
                                                      · rcases p673_3 (m.d 2 5) (by simp) with h678 | h678
                                                        · linarith only [h4, h678, hlam]
                                                        · linarith only [h498, h678, hlam]
                                                    · linarith only [h675, hlam, p673_0]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p621_1, p673_1]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    rcases p673_3 (m.d 0 5) (by simp) with h683 | h683
                                                    · rcases p673_3 (m.d 1 5) (by simp) with h684 | h684
                                                      · linarith only [h0, h4, h498, h684, hc01, hlam, hphi, u0ehi4]
                                                      · linarith only [h501, h684, hlam]
                                                    · linarith only [h6, h683, hlam]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    rcases p673_3 (m.d 0 5) (by simp) with h688 | h688
                                                    · rcases p673_3 (m.d 1 5) (by simp) with h689 | h689
                                                      · linarith only [h502, h689, hlam, p673_1]
                                                      · rcases p673_3 (m.d 2 5) (by simp) with h691 | h691
                                                        · linarith only [h4, h691, hlam]
                                                        · linarith only [h618, h691, hlam]
                                                    · linarith only [h688, h7, hlam]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h502, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p673_1, u0ehi4]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [hlam, p673_0]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h498, hlam, p673_0]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h1, h501, hc01, hlam, hphi, ht0b, ht5b, p673_1, u5ehi3]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h502, hlam, p673_1]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h4, hlam, p673_1]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h0, h2, h616, h618, hc01, hlam, hphi, ht0b, ht5b, p673_1, u5ehi1]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [hlam, p673_0]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h0, h2, h616, h618, hc01, hlam, hphi, ht0b, ht5b, p673_1, u5ehi3]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h0, h2, h616, h618, hc01, hlam, hphi, ht0b, ht5b, p673_1, u5ehi4]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h6, hlam, p673_1]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h501, hlam, p673_1]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h617, hlam, p673_0]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [hlam, p673_0]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h619, hlam, p673_1]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h7, hlam, p673_0]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h0, h2, h5, h501, h7, hc01, hlam, hphi, ht0b, ht5b, p673_1, u5ehi3]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h618, hlam, p673_0]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [h0, h2, h616, h618, hc01, hlam, hphi, ht0b, ht5b, p673_1, u5ehi3]
                                                  · have p673_0 := h673c.1
                                                    have p673_1 := h673c.2.1
                                                    have p673_2 := h673c.2.2.1
                                                    have p673_3 := h673c.2.2.2
                                                    linarith only [hlam, p673_0]
                                                · linarith only [h672, hlam, p621_0]
                                              · linarith only [h435, h671, hlam]
                                            · linarith only [h670, h8, hlam]
                                        · linarith only [h0, h667, hlam]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h617, hlam, p621_1]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [h618, hlam, p621_1]
                                      · have p621_0 := h621c.1
                                        have p621_1 := h621c.2.1
                                        have p621_2 := h621c.2.2.1
                                        have p621_3 := h621c.2.2.2
                                        linarith only [hlam, p621_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h722 | h722
                                    · linarith only [h0, h2, h435, h5, h618, h722, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                    · rcases h2bigk with h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h2, h435, h5, h618, h7, hlam, p724_2]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h0, h501, h8, hc01, hlam, hphi, ht0b, ht5b, p724_1, u5ehi3]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        rcases p724_3 (m.d 0 2) (by simp) with h728 | h728
                                        · rcases p724_3 (m.d 1 2) (by simp) with h729 | h729
                                          · linarith only [h0, h729, hlam]
                                          · rcases p724_3 (m.d 2 3) (by simp) with h731 | h731
                                            · linarith only [h2, h731, hlam]
                                            · linarith only [h616, h731, hlam]
                                        · linarith only [h728, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        rcases p724_3 (m.d 0 2) (by simp) with h735 | h735
                                        · rcases p724_3 (m.d 1 2) (by simp) with h736 | h736
                                          · linarith only [h0, h736, hlam]
                                          · rcases p724_3 (m.d 2 3) (by simp) with h738 | h738
                                            · linarith only [h2, h738, hlam]
                                            · linarith only [h617, h738, hlam]
                                        · linarith only [h735, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h0, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h8, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h435, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h498, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h2, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        rcases p724_3 (m.d 0 2) (by simp) with h748 | h748
                                        · rcases p724_3 (m.d 1 2) (by simp) with h749 | h749
                                          · linarith only [h749, hlam, p724_0]
                                          · rcases p724_3 (m.d 2 3) (by simp) with h751 | h751
                                            · rcases p724_3 (m.d 2 4) (by simp) with h752 | h752
                                              · linarith only [h616, h752, hlam]
                                              · linarith only [h435, h752, hlam]
                                            · linarith only [h751, hlam, p724_0]
                                        · linarith only [h0, h748, hlam]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h435, hc12, hc23, hlam, hphi, p724_1]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p724_1, u5ehi2]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h3, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h0, h2, h5, h618, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p724_1]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h616, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h618, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h4, hlam, p724_0]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        rcases p724_3 (m.d 0 2) (by simp) with h766 | h766
                                        · rcases p724_3 (m.d 1 2) (by simp) with h767 | h767
                                          · linarith only [h767, hlam, p724_0]
                                          · rcases p724_3 (m.d 2 3) (by simp) with h769 | h769
                                            · rcases p724_3 (m.d 2 4) (by simp) with h770 | h770
                                              · linarith only [h618, h770, hlam]
                                              · linarith only [h435, h770, hlam]
                                            · linarith only [h769, h8, hlam]
                                        · linarith only [h0, h766, hlam]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h617, hlam, p724_1]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [h0, h4, h435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p724_1]
                                      · have p724_0 := h724c.1
                                        have p724_1 := h724c.2.1
                                        have p724_2 := h724c.2.2.1
                                        have p724_3 := h724c.2.2.2
                                        linarith only [hlam, p724_0]
                                · linarith only [h1, h501, h617, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h0, h2, h5, h500, h501, h502, h616, h7, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h780 | h780
                            · linarith only [h0, h2, h500, h501, h6, h780, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h782 | h782
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h783 | h783
                                · linarith only [h0, h2, h500, h501, h783, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h785 | h785
                                  · linarith only [h0, h2, h6, h780, h782, h783, h785, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h787 | h787
                                    · linarith only [h1, h500, h785, h787, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                                    · rcases h2bigk with h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h2, h5, h7, h783, h787, h8, hlam, p789_2]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        rcases p789_3 (m.d 0 2) (by simp) with h792 | h792
                                        · rcases p789_3 (m.d 1 2) (by simp) with h793 | h793
                                          · linarith only [h0, h793, hlam]
                                          · rcases p789_3 (m.d 2 3) (by simp) with h795 | h795
                                            · linarith only [h795, hlam, p789_0]
                                            · rcases p789_3 (m.d 2 4) (by simp) with h797 | h797
                                              · linarith only [h3, h797, hlam]
                                              · rcases p789_3 (m.d 2 5) (by simp) with h799 | h799
                                                · linarith only [h4, h799, hlam]
                                                · linarith only [h783, h799, hlam]
                                        · linarith only [h792, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        rcases p789_3 (m.d 0 2) (by simp) with h803 | h803
                                        · rcases p789_3 (m.d 1 2) (by simp) with h804 | h804
                                          · linarith only [h0, h804, hlam]
                                          · rcases p789_3 (m.d 2 3) (by simp) with h806 | h806
                                            · linarith only [h2, h806, hlam]
                                            · linarith only [h782, h806, hlam]
                                        · linarith only [h803, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        rcases p789_3 (m.d 0 2) (by simp) with h810 | h810
                                        · rcases p789_3 (m.d 1 2) (by simp) with h811 | h811
                                          · linarith only [h0, h811, hlam]
                                          · rcases p789_3 (m.d 2 3) (by simp) with h813 | h813
                                            · linarith only [h2, h813, hlam]
                                            · rcases p789_3 (m.d 2 4) (by simp) with h815 | h815
                                              · linarith only [h3, h815, hlam]
                                              · rcases p789_3 (m.d 2 5) (by simp) with h817 | h817
                                                · linarith only [h817, hlam, p789_0]
                                                · rcases h5bigk with h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    rcases p819_3 (m.d 0 5) (by simp) with h821 | h821
                                                    · rcases p819_3 (m.d 1 5) (by simp) with h822 | h822
                                                      · linarith only [h822, hlam, p819_0]
                                                      · rcases p819_3 (m.d 2 5) (by simp) with h824 | h824
                                                        · linarith only [h4, h824, hlam]
                                                        · linarith only [h498, h824, hlam]
                                                    · linarith only [h821, hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    rcases p819_3 (m.d 0 5) (by simp) with h828 | h828
                                                    · rcases p819_3 (m.d 1 5) (by simp) with h829 | h829
                                                      · linarith only [h498, h829, hlam, p819_1]
                                                      · rcases p819_3 (m.d 2 5) (by simp) with h831 | h831
                                                        · linarith only [h4, h831, hlam]
                                                        · rcases p819_3 (m.d 3 5) (by simp) with h833 | h833
                                                          · linarith only [h6, h833, hlam]
                                                          · linarith only [h783, h833, hlam]
                                                    · linarith only [h4, h828, hlam]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h0, h2, h435, h5, h7, h782, h783, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h0, h2, h435, h5, h7, h782, h783, h787, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hc15, hlam, hphi, ht01, p819_1, u0ehi4]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h498, hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h501, hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h780, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h4, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p789_1, p819_1, u5ehi1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h783, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h785, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h6, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h0, h2, h6, hc01, hlam, hphi, ht0b, ht5b, p819_1, u5ehi1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h0, h2, h5, h7, h787, hc01, hlam, hphi, ht0b, ht5b, p819_1, u5ehi2]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h787, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h7, hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h0, h2, h5, h7, hc01, hlam, hphi, ht0b, ht5b, p819_1, u5ehi1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h0, h2, h435, h5, h7, h782, h783, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h0, h2, h5, h7, hc01, hlam, hphi, ht0b, ht5b, p819_1, u5ehi3]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hlam, p819_0]
                                        · linarith only [h810, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h0, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h8, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h435, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h498, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h2, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h783, hc12, hc35, hlam, hphi, ht23, p789_1]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h0, h2, h435, h6, h783, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p789_1]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h783, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h3, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h0, h2, h6, h782, h783, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p789_1]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h782, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h785, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h4, hlam, p789_0]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        rcases p789_3 (m.d 0 2) (by simp) with h876 | h876
                                        · rcases p789_3 (m.d 1 2) (by simp) with h877 | h877
                                          · linarith only [h877, hlam, p789_0]
                                          · rcases p789_3 (m.d 2 3) (by simp) with h879 | h879
                                            · linarith only [h783, h879, hlam]
                                            · linarith only [h8, h879, hlam]
                                        · linarith only [h0, h876, hlam]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h0, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p789_1]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [h0, h2, h435, h5, h7, h783, h787, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p789_1]
                                      · have p789_0 := h789c.1
                                        have p789_1 := h789c.2.1
                                        have p789_2 := h789c.2.2.1
                                        have p789_3 := h789c.2.2.2
                                        linarith only [hlam, p789_0]
                              · linarith only [h1, h500, h782, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h887 | h887
                          · linarith only [h0, h2, h5, h500, h887, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h889 | h889
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h890 | h890
                              · linarith only [h0, h2, h500, h889, h890, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h892 | h892
                                · linarith only [h887, h890, h892, hc13, hc34, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h894 | h894
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h895 | h895
                                    · rcases h2bigk with h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h2, h5, h8, h892, h895, hlam, p896_2]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        rcases p896_3 (m.d 0 2) (by simp) with h899 | h899
                                        · rcases p896_3 (m.d 1 2) (by simp) with h900 | h900
                                          · linarith only [h0, h900, hlam]
                                          · rcases p896_3 (m.d 2 3) (by simp) with h902 | h902
                                            · linarith only [h902, hlam, p896_0]
                                            · rcases p896_3 (m.d 2 4) (by simp) with h904 | h904
                                              · linarith only [h3, h904, hlam]
                                              · linarith only [h890, h904, hlam]
                                        · linarith only [h899, hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h0, h435, h889, hc01, hlam, hphi, ht0b, ht5b, p896_1, u5ehi4]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        rcases p896_3 (m.d 0 2) (by simp) with h909 | h909
                                        · rcases p896_3 (m.d 1 2) (by simp) with h910 | h910
                                          · linarith only [h0, h910, hlam]
                                          · rcases p896_3 (m.d 2 3) (by simp) with h912 | h912
                                            · linarith only [h2, h912, hlam]
                                            · rcases p896_3 (m.d 2 4) (by simp) with h914 | h914
                                              · linarith only [h3, h914, hlam]
                                              · linarith only [h894, h914, hlam]
                                        · linarith only [h909, hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h0, hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h8, hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h435, hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h498, hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h2, hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h0, h2, h5, h892, h895, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p896_1]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h890, hlam, p896_1]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h892, hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h3, hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        rcases p896_3 (m.d 0 2) (by simp) with h929 | h929
                                        · rcases p896_3 (m.d 1 2) (by simp) with h930 | h930
                                          · linarith only [h930, hlam, p896_0]
                                          · rcases p896_3 (m.d 2 3) (by simp) with h932 | h932
                                            · linarith only [h890, h932, hlam]
                                            · linarith only [h8, h932, hlam]
                                        · linarith only [h0, h929, hlam]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h8, hc12, hc24, hlam, hphi, p896_1]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h0, h2, h498, h5, h890, hc01, hlam, hphi, ht0b, ht5b, p896_1, u5ehi1]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h4, hlam, p896_0]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        rcases p896_3 (m.d 0 2) (by simp) with h940 | h940
                                        · rcases p896_3 (m.d 1 2) (by simp) with h941 | h941
                                          · linarith only [h941, hlam, p896_0]
                                          · rcases p896_3 (m.d 2 3) (by simp) with h943 | h943
                                            · linarith only [h892, h943, hlam]
                                            · linarith only [h8, h943, hlam]
                                        · linarith only [h0, h940, hlam]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h8, hc12, hc25, hlam, hphi, p896_1]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [h894, hlam, p896_1]
                                      · have p896_0 := h896c.1
                                        have p896_1 := h896c.2.1
                                        have p896_2 := h896c.2.2.1
                                        have p896_3 := h896c.2.2.2
                                        linarith only [hlam, p896_0]
                                    · linarith only [h435, h889, h890, h895, hlam]
                                  · linarith only [h435, h889, h894, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h952 | h952
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h953 | h953
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h954 | h954
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h955 | h955
                                    · linarith only [h0, h2, h889, h952, h955, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · linarith only [h500, h8, h954, h955, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h958 | h958
                                    · linarith only [h0, h2, h435, h5, h954, h958, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                    · rcases h2bigk with h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h2, h5, h500, h7, h8, h952, h954, hlam, p960_2]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h0, h887, h953, hc01, hlam, hphi, ht0b, ht5b, p960_1, u5ehi1]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        rcases p960_3 (m.d 0 2) (by simp) with h964 | h964
                                        · rcases p960_3 (m.d 1 2) (by simp) with h965 | h965
                                          · linarith only [h0, h965, hlam]
                                          · rcases p960_3 (m.d 2 3) (by simp) with h967 | h967
                                            · linarith only [h2, h967, hlam]
                                            · linarith only [h952, h967, hlam]
                                        · linarith only [h964, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        rcases p960_3 (m.d 0 2) (by simp) with h971 | h971
                                        · rcases p960_3 (m.d 1 2) (by simp) with h972 | h972
                                          · linarith only [h0, h972, hlam]
                                          · rcases p960_3 (m.d 2 3) (by simp) with h974 | h974
                                            · linarith only [h2, h974, hlam]
                                            · linarith only [h953, h974, hlam]
                                        · linarith only [h971, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h0, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h8, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h435, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h498, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h2, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        rcases p960_3 (m.d 0 2) (by simp) with h984 | h984
                                        · rcases p960_3 (m.d 1 2) (by simp) with h985 | h985
                                          · linarith only [h985, hlam, p960_0]
                                          · rcases p960_3 (m.d 2 3) (by simp) with h987 | h987
                                            · rcases p960_3 (m.d 2 4) (by simp) with h988 | h988
                                              · linarith only [h952, h988, hlam]
                                              · linarith only [h435, h988, hlam]
                                            · linarith only [h987, hlam, p960_0]
                                        · linarith only [h0, h984, hlam]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h0, h2, h500, h8, h952, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p960_1]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p960_1, u5ehi2]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h3, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h0, h2, h5, h7, h954, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p960_1]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h952, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h954, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h4, hlam, p960_0]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        rcases p960_3 (m.d 0 2) (by simp) with h1002 | h1002
                                        · rcases p960_3 (m.d 1 2) (by simp) with h1003 | h1003
                                          · linarith only [h1003, hlam, p960_0]
                                          · rcases p960_3 (m.d 2 3) (by simp) with h1005 | h1005
                                            · rcases p960_3 (m.d 2 4) (by simp) with h1006 | h1006
                                              · linarith only [h1006, h954, hlam]
                                              · linarith only [h1006, h435, hlam]
                                            · linarith only [h1005, h8, hlam]
                                        · linarith only [h0, h1002, hlam]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h953, hlam, p960_1]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [h435, hc12, hc25, hlam, hphi, p960_1]
                                      · have p960_0 := h960c.1
                                        have p960_1 := h960c.2.1
                                        have p960_2 := h960c.2.2.1
                                        have p960_3 := h960c.2.2.2
                                        linarith only [hlam, p960_0]
                                · linarith only [h0, h2, h500, h6, h8, h952, h953, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1015 | h1015
                                · linarith only [h0, h1015, h2, h5, h952, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1017 | h1017
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1018 | h1018
                                    · rcases h2bigk with h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h1017, h3, h500, h8, h889, hlam, p1019_2]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        rcases p1019_3 (m.d 0 2) (by simp) with h1022 | h1022
                                        · rcases p1019_3 (m.d 1 2) (by simp) with h1023 | h1023
                                          · linarith only [h0, h1023, hlam]
                                          · rcases p1019_3 (m.d 2 3) (by simp) with h1025 | h1025
                                            · linarith only [h1025, hlam, p1019_0]
                                            · rcases p1019_3 (m.d 2 4) (by simp) with h1027 | h1027
                                              · linarith only [h1027, h3, hlam]
                                              · linarith only [h1027, h952, hlam]
                                        · linarith only [h1022, hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h0, h1017, h500, h8, h889, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1019_1]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        rcases p1019_3 (m.d 0 2) (by simp) with h1032 | h1032
                                        · rcases p1019_3 (m.d 1 2) (by simp) with h1033 | h1033
                                          · linarith only [h0, h1033, hlam]
                                          · rcases p1019_3 (m.d 2 3) (by simp) with h1035 | h1035
                                            · linarith only [h1035, h2, hlam]
                                            · rcases p1019_3 (m.d 2 4) (by simp) with h1037 | h1037
                                              · linarith only [h1037, h3, hlam]
                                              · linarith only [h1017, h1037, hlam]
                                        · linarith only [h1032, hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h0, hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h8, hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h435, hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h498, hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h2, hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h0, h1015, h1018, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1019_1]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h952, hlam, p1019_1]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h1015, hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h3, hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        rcases p1019_3 (m.d 0 2) (by simp) with h1052 | h1052
                                        · rcases p1019_3 (m.d 1 2) (by simp) with h1053 | h1053
                                          · linarith only [h1053, hlam, p1019_0]
                                          · rcases p1019_3 (m.d 2 3) (by simp) with h1055 | h1055
                                            · linarith only [h1055, h952, hlam]
                                            · linarith only [h1055, h8, hlam]
                                        · linarith only [h0, h1052, hlam]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h0, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1019_1]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h0, h2, h5, h952, hc01, hlam, hphi, ht0b, ht5b, p1019_1, u5ehi2]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h4, hlam, p1019_0]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        rcases p1019_3 (m.d 0 2) (by simp) with h1063 | h1063
                                        · rcases p1019_3 (m.d 1 2) (by simp) with h1064 | h1064
                                          · linarith only [h1064, hlam, p1019_0]
                                          · rcases p1019_3 (m.d 2 3) (by simp) with h1066 | h1066
                                            · linarith only [h1015, h1066, hlam]
                                            · linarith only [h1066, h8, hlam]
                                        · linarith only [h0, h1063, hlam]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h8, hc12, hc25, hlam, hphi, p1019_1]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [h1017, hlam, p1019_1]
                                      · have p1019_0 := h1019c.1
                                        have p1019_1 := h1019c.2.1
                                        have p1019_2 := h1019c.2.2.1
                                        have p1019_3 := h1019c.2.2.2
                                        linarith only [hlam, p1019_0]
                                    · linarith only [h0, h1018, h2, h5, h7, h8, h952, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1074 | h1074
                                    · linarith only [h1017, h1074, h435, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h1074, h8, h952, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
              · linarith only [h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc25, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h2, h3, hc24, hlam, hphi, ht01, ht12, u0ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc13, hlam, hphi, ht01, u0ehi0]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT2_M_LI_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h5elo := hb5.1
  have h2bigk := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h0, h11, h13, h8, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h13, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h10, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h3, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h19, h2, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
                    · linarith only [h0, h2, h21, h7, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h21, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h6, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h5, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h27 | h27
          · rcases m.htr 0 3 5 (by decide) (by decide) with h28 | h28
            · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
                  · linarith only [h0, h3, h31, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                        · linarith only [h0, h30, h35, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                          · linarith only [h0, h30, h37, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h37, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h31, h34, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h27, h30, h33, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h2, h3, h30, hc12, hc24, hlam, hphi]
              · linarith only [h29, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h28, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h27, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h46 | h46
        · rcases m.htr 0 2 5 (by decide) (by decide) with h47 | h47
          · rcases m.htr 0 3 5 (by decide) (by decide) with h48 | h48
            · rcases m.htr 0 4 5 (by decide) (by decide) with h49 | h49
              · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
                · linarith only [h0, h2, h46, h50, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                            · linarith only [h0, h52, h57, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h55, h57, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h2, h56, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h2, h46, h55, hlam]
                      · linarith only [h54, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h53, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h2, h46, h52, hc12, hc23, hlam, hphi]
              · linarith only [h49, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h2, h48, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h46, h47, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h68 | h68
          · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
            · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
              · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                · linarith only [h0, h2, h68, h71, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                  · linarith only [h0, h46, h73, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h78 | h78
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h79 | h79
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                              · rcases h0bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [hlam, p81_0]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h0, h75, h78, h80, hc45, hlam, hphi, ht0b, ht5b, p81_1, u0elo0]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h0, h2, h75, h78, h80, hc45, hlam, hphi, ht0b, ht5b, p81_1, u0elo0]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h0, h46, h75, h78, h80, hc45, hlam, hphi, ht0b, ht5b, p81_1, u0elo0]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  rcases p81_3 (m.d 0 1) (by simp) with h86 | h86
                                  · rcases p81_3 (m.d 0 2) (by simp) with h87 | h87
                                    · linarith only [h0, h87, hlam]
                                    · linarith only [h68, h87, hlam]
                                  · linarith only [h1, h86, hlam]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h0, hlam, p81_1]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [hlam, p81_0]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h2, hlam, p81_1]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h46, hlam, p81_1]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  rcases p81_3 (m.d 0 1) (by simp) with h95 | h95
                                  · rcases p81_3 (m.d 0 2) (by simp) with h96 | h96
                                    · rcases p81_3 (m.d 0 3) (by simp) with h97 | h97
                                      · rcases p81_3 (m.d 0 4) (by simp) with h98 | h98
                                        · rcases p81_3 (m.d 0 5) (by simp) with h99 | h99
                                          · linarith only [h68, h99, hlam]
                                          · rcases h2bigk with h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h46, h77, hc12, hc23, hlam, hphi, p101_1]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h2, hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h46, hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              rcases p101_3 (m.d 0 2) (by simp) with h106 | h106
                                              · rcases p101_3 (m.d 1 2) (by simp) with h107 | h107
                                                · linarith only [h0, h107, hlam]
                                                · linarith only [h107, h75, hlam]
                                              · linarith only [h106, hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h0, hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h71, hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h73, hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h0, h78, h80, hc45, hlam, hphi, ht0b, ht5b, p101_1, u0elo0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h1, h75, h78, h80, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p101_1, p81_1]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              rcases p101_3 (m.d 0 2) (by simp) with h117 | h117
                                              · linarith only [h117, h2, hlam]
                                              · linarith only [h0, h117, hlam]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h1, h46, h75, h78, h80, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p101_1, p81_1]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h1, h2, h75, hlam, p101_2, p81_1]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h1, h75, h78, h80, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p101_1, p81_1]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              rcases p101_3 (m.d 0 2) (by simp) with h124 | h124
                                              · linarith only [h124, h46, hlam]
                                              · linarith only [h0, h124, hlam]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h77, hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h1, h46, h75, hlam, p101_2, p81_1]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h68, hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h75, hlam, p101_0]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h78, hlam, p101_1]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [h79, hlam, p101_1]
                                            · have p101_0 := h101c.1
                                              have p101_1 := h101c.2.1
                                              have p101_2 := h101c.2.2.1
                                              have p101_3 := h101c.2.2.2
                                              linarith only [hlam, p101_0]
                                        · linarith only [h70, h98, hlam]
                                      · linarith only [h69, h97, hlam]
                                    · linarith only [h68, h96, hlam]
                                  · linarith only [h1, h95, hlam]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p81_1, u0elo2]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h68, h78, h80, hc45, hlam, hphi, ht0b, ht5b, p81_1, u0elo2]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [hlam, p81_0]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h0, h46, h75, h78, h80, hc45, hlam, hphi, ht0b, ht5b, p81_1, u0elo2]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  rcases p81_3 (m.d 0 1) (by simp) with h143 | h143
                                  · rcases p81_3 (m.d 0 2) (by simp) with h144 | h144
                                    · linarith only [h144, h2, hlam]
                                    · linarith only [h144, h68, hlam]
                                  · linarith only [h1, h143, hlam]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h0, h75, h78, h80, hc45, hlam, hphi, ht0b, ht5b, p81_1, u0elo3]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h0, h75, h78, h80, hc45, hlam, hphi, ht0b, ht5b, p81_1, u0elo3]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h0, h2, h75, h78, h80, hc45, hlam, hphi, ht0b, ht5b, p81_1, u0elo3]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [hlam, p81_0]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  rcases p81_3 (m.d 0 1) (by simp) with h152 | h152
                                  · rcases p81_3 (m.d 0 2) (by simp) with h153 | h153
                                    · linarith only [h153, h46, hlam]
                                    · linarith only [h153, h68, hlam]
                                  · linarith only [h1, h152, hlam]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h1, hlam, p81_1]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h68, hlam, p81_0]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h69, hlam, p81_0]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [h70, hlam, p81_0]
                                · have p81_0 := h81c.1
                                  have p81_1 := h81c.2.1
                                  have p81_2 := h81c.2.2.1
                                  have p81_3 := h81c.2.2.2
                                  linarith only [hlam, p81_0]
                              · linarith only [h80, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h1, h46, h76, h79, hc04, hlam, hphi, ht45, u5elo0]
                          · linarith only [h46, h77, h78, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h165 | h165
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h167 | h167
                              · rcases h0bigk with h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [hlam, p168_0]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h0, h75, hc25, hlam, hphi, ht0b, ht5b, p168_1, u0elo0]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h0, h165, h167, h2, h75, hc45, hlam, hphi, ht0b, ht5b, p168_1, u0elo0]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h0, h165, h167, h46, h75, hc45, hlam, hphi, ht0b, ht5b, p168_1, u0elo0]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  rcases p168_3 (m.d 0 1) (by simp) with h173 | h173
                                  · rcases p168_3 (m.d 0 2) (by simp) with h174 | h174
                                    · linarith only [h0, h174, hlam]
                                    · linarith only [h174, h68, hlam]
                                  · linarith only [h1, h173, hlam]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h0, hlam, p168_1]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [hlam, p168_0]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h2, hlam, p168_1]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h46, hlam, p168_1]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h1, h165, h167, h2, h75, h77, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p168_1]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1, u0elo2]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h0, h2, h77, hc12, hc34, hlam, hphi, ht23, p168_1]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [hlam, p168_0]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h0, h165, h167, h2, h46, h75, h77, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p168_1]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  rcases p168_3 (m.d 0 1) (by simp) with h187 | h187
                                  · rcases p168_3 (m.d 0 2) (by simp) with h188 | h188
                                    · linarith only [h188, h2, hlam]
                                    · linarith only [h188, h68, hlam]
                                  · linarith only [h1, h187, hlam]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h0, h165, h167, h75, hc45, hlam, hphi, ht0b, ht5b, p168_1, u0elo3]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h0, h165, h167, h75, hc45, hlam, hphi, ht0b, ht5b, p168_1, u0elo3]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h0, h165, h167, h2, h75, hc45, hlam, hphi, ht0b, ht5b, p168_1, u0elo3]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [hlam, p168_0]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  rcases p168_3 (m.d 0 1) (by simp) with h196 | h196
                                  · rcases p168_3 (m.d 0 2) (by simp) with h197 | h197
                                    · linarith only [h197, h46, hlam]
                                    · linarith only [h197, h68, hlam]
                                  · linarith only [h1, h196, hlam]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h1, hlam, p168_1]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h68, hlam, p168_0]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h69, hlam, p168_0]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [h70, hlam, p168_0]
                                · have p168_0 := h168c.1
                                  have p168_1 := h168c.2.1
                                  have p168_2 := h168c.2.2.1
                                  have p168_3 := h168c.2.2.2
                                  linarith only [hlam, p168_0]
                              · linarith only [h167, h77, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h1, h166, h46, h76, hc04, hlam, hphi, ht45, u5elo0]
                          · linarith only [h0, h165, h2, h75, hc25, hlam, hphi, u5elo3]
                      · linarith only [h76, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h75, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h70, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h69, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h68, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h1, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h215 | h215
    · rcases m.htr 0 2 3 (by decide) (by decide) with h216 | h216
      · rcases m.htr 0 2 4 (by decide) (by decide) with h217 | h217
        · rcases m.htr 0 2 5 (by decide) (by decide) with h218 | h218
          · rcases m.htr 0 3 5 (by decide) (by decide) with h219 | h219
            · rcases m.htr 0 4 5 (by decide) (by decide) with h220 | h220
              · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h224 | h224
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h228 | h228
                              · linarith only [h216, h225, h228, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h228, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h224, h227, hc24, hlam, hphi, ht45, u5elo1]
                          · linarith only [h226, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h233 | h233
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h234 | h234
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h235 | h235
                              · rcases h0bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [hlam, p236_0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h0, hlam, p236_0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h216, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p236_1, u0elo0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h217, h225, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p236_1, u0elo0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  rcases p236_3 (m.d 0 1) (by simp) with h241 | h241
                                  · rcases p236_3 (m.d 0 2) (by simp) with h242 | h242
                                    · rcases p236_3 (m.d 0 3) (by simp) with h243 | h243
                                      · rcases p236_3 (m.d 0 4) (by simp) with h244 | h244
                                        · rcases p236_3 (m.d 0 5) (by simp) with h245 | h245
                                          · linarith only [h215, h245, hlam]
                                          · rcases h2bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h0, hlam, p247_1]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h233, h235, hc45, hlam, hphi, ht0b, ht5b, p247_1, u0elo1]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h225, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p247_1, u0elo1]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              rcases p247_3 (m.d 0 2) (by simp) with h252 | h252
                                              · rcases p247_3 (m.d 1 2) (by simp) with h253 | h253
                                                · rcases p247_3 (m.d 2 3) (by simp) with h254 | h254
                                                  · linarith only [h216, h254, hlam]
                                                  · linarith only [h233, h254, hlam]
                                                · linarith only [h223, h253, hlam]
                                              · linarith only [h252, hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p236_1, p247_1]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              rcases p247_3 (m.d 0 2) (by simp) with h261 | h261
                                              · linarith only [h0, h261, hlam]
                                              · linarith only [h216, h261, hlam]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              rcases p247_3 (m.d 0 2) (by simp) with h264 | h264
                                              · linarith only [h0, h264, hlam]
                                              · linarith only [h217, h264, hlam]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h0, h215, h223, hlam, p236_1, p247_2]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h216, hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h221, hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h225, hlam, p247_1]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h216, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p247_1, u0elo1]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h217, hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h222, hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h217, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1, u0elo1]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h217, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p247_1, u0elo1]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h218, hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h223, hlam, p247_0]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h233, hlam, p247_1]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [h234, hlam, p247_1]
                                            · have p247_0 := h247c.1
                                              have p247_1 := h247c.2.1
                                              have p247_2 := h247c.2.2.1
                                              have p247_3 := h247c.2.2.2
                                              linarith only [hlam, p247_0]
                                        · linarith only [h220, h244, hlam]
                                      · linarith only [h219, h243, hlam]
                                    · linarith only [h218, h242, hlam]
                                  · linarith only [h215, h241, hlam]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h215, h223, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p236_1, u0elo1]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [hlam, p236_0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h216, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p236_1, u0elo1]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h220, hc45, hlam, hphi, ht0b, ht5b, p236_1, u0elo1]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  rcases p236_3 (m.d 0 1) (by simp) with h291 | h291
                                  · linarith only [h0, h291, hlam]
                                  · linarith only [h215, h291, hlam]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h215, h223, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p236_1, u0elo2]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h216, hlam, p236_0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [hlam, p236_0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h216, h217, h225, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p236_1, u0elo1]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  rcases p236_3 (m.d 0 1) (by simp) with h298 | h298
                                  · rcases p236_3 (m.d 0 2) (by simp) with h299 | h299
                                    · rcases p236_3 (m.d 0 3) (by simp) with h300 | h300
                                      · rcases p236_3 (m.d 0 4) (by simp) with h301 | h301
                                        · rcases p236_3 (m.d 0 5) (by simp) with h302 | h302
                                          · linarith only [h219, h302, hlam]
                                          · rcases h2bigk with h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h0, hlam, p304_1]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h233, h235, hc45, hlam, hphi, ht0b, ht5b, p304_1, u0elo1]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h225, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p304_1, u0elo1]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              rcases p304_3 (m.d 0 2) (by simp) with h309 | h309
                                              · rcases p304_3 (m.d 1 2) (by simp) with h310 | h310
                                                · rcases p304_3 (m.d 2 3) (by simp) with h311 | h311
                                                  · linarith only [h216, h311, hlam]
                                                  · linarith only [h233, h311, hlam]
                                                · linarith only [h223, h310, hlam]
                                              · linarith only [h309, hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h0, h215, h223, h233, h235, h298, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p236_1, p304_1]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              rcases p304_3 (m.d 0 2) (by simp) with h318 | h318
                                              · linarith only [h0, h318, hlam]
                                              · linarith only [h216, h318, hlam]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              rcases p304_3 (m.d 0 2) (by simp) with h321 | h321
                                              · linarith only [h0, h321, hlam]
                                              · linarith only [h217, h321, hlam]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h0, h215, h223, h298, hlam, p236_1, p304_2]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h216, hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h221, hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h225, hlam, p304_1]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h216, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p304_1, u0elo1]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h217, hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h222, hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h217, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p304_1, u0elo1]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h217, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p304_1, u0elo1]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h218, hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h223, hlam, p304_0]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h233, hlam, p304_1]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [h234, hlam, p304_1]
                                            · have p304_0 := h304c.1
                                              have p304_1 := h304c.2.1
                                              have p304_2 := h304c.2.2.1
                                              have p304_3 := h304c.2.2.2
                                              linarith only [hlam, p304_0]
                                        · linarith only [h220, h301, hlam]
                                      · linarith only [h219, h300, hlam]
                                    · linarith only [h218, h299, hlam]
                                  · linarith only [h215, h298, hlam]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h215, h223, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p236_1, u0elo3]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h217, hlam, p236_0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h216, h217, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p236_1, u0elo1]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [hlam, p236_0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  rcases p236_3 (m.d 0 1) (by simp) with h348 | h348
                                  · rcases p236_3 (m.d 0 2) (by simp) with h349 | h349
                                    · rcases p236_3 (m.d 0 3) (by simp) with h350 | h350
                                      · rcases p236_3 (m.d 0 4) (by simp) with h351 | h351
                                        · rcases p236_3 (m.d 0 5) (by simp) with h352 | h352
                                          · linarith only [h220, h352, hlam]
                                          · rcases h2bigk with h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h0, hlam, p354_1]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h233, h235, hc45, hlam, hphi, ht0b, ht5b, p354_1, u0elo1]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h225, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p354_1, u0elo1]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              rcases p354_3 (m.d 0 2) (by simp) with h359 | h359
                                              · rcases p354_3 (m.d 1 2) (by simp) with h360 | h360
                                                · rcases p354_3 (m.d 2 3) (by simp) with h361 | h361
                                                  · linarith only [h216, h361, hlam]
                                                  · linarith only [h233, h361, hlam]
                                                · linarith only [h223, h360, hlam]
                                              · linarith only [h359, hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h0, h215, h223, h233, h235, h348, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p236_1, p354_1]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              rcases p354_3 (m.d 0 2) (by simp) with h368 | h368
                                              · linarith only [h0, h368, hlam]
                                              · linarith only [h216, h368, hlam]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              rcases p354_3 (m.d 0 2) (by simp) with h371 | h371
                                              · linarith only [h0, h371, hlam]
                                              · linarith only [h217, h371, hlam]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h0, h215, h223, h348, hlam, p236_1, p354_2]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h216, hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h221, hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h225, hlam, p354_1]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h216, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p354_1, u0elo1]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h217, hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h222, hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h217, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p354_1, u0elo1]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h217, h233, h235, hc45, hlam, hphi, ht0b, ht5b, p354_1, u0elo1]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h218, hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h223, hlam, p354_0]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h233, hlam, p354_1]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [h234, hlam, p354_1]
                                            · have p354_0 := h354c.1
                                              have p354_1 := h354c.2.1
                                              have p354_2 := h354c.2.2.1
                                              have p354_3 := h354c.2.2.2
                                              linarith only [hlam, p354_0]
                                        · linarith only [h220, h351, hlam]
                                      · linarith only [h219, h350, hlam]
                                    · linarith only [h218, h349, hlam]
                                  · linarith only [h215, h348, hlam]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h215, hlam, p236_1]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h218, hlam, p236_0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h219, hlam, p236_0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [h220, hlam, p236_0]
                                · have p236_0 := h236c.1
                                  have p236_1 := h236c.2.1
                                  have p236_2 := h236c.2.2.1
                                  have p236_3 := h236c.2.2.2
                                  linarith only [hlam, p236_0]
                              · linarith only [h225, h233, h235, hc35, hlam, hphi, u5elo4]
                            · linarith only [h215, h224, h234, hc24, hlam, hphi, ht45, u5elo0]
                          · linarith only [h233, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h224, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h223, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h217, h222, hlam]
                · linarith only [h0, h216, h221, hlam]
              · linarith only [h220, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h219, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h216, h218, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h409 | h409
          · rcases m.htr 0 3 5 (by decide) (by decide) with h410 | h410
            · rcases m.htr 0 4 5 (by decide) (by decide) with h411 | h411
              · rcases m.htr 1 2 3 (by decide) (by decide) with h412 | h412
                · rcases m.htr 1 2 4 (by decide) (by decide) with h413 | h413
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h414 | h414
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h415 | h415
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h416 | h416
                        · linarith only [h216, h217, h413, h416, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h418 | h418
                          · linarith only [h216, h217, h413, h418, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h418, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h217, h413, h415, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h217, h413, h414, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h423 | h423
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h424 | h424
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h425 | h425
                        · linarith only [h0, h216, h413, h425, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h427 | h427
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h428 | h428
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h429 | h429
                              · rcases h0bigk with h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, h413, h425, hc03, hc34, hlam, hphi, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, h413, h425, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, h413, h425, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, h413, h425, hc01, hc34, hlam, hphi, ht12, ht23, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, h413, h425, hc03, hc34, hlam, hphi, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h217, hlam, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  rcases p430_3 (m.d 0 1) (by simp) with h440 | h440
                                  · linarith only [h0, h440, hlam]
                                  · linarith only [h215, h440, hlam]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h215, h423, h427, h429, hc45, hlam, hphi, ht0b, ht5b, p430_1, u0elo2]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h216, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h216, h217, hlam, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  rcases p430_3 (m.d 0 1) (by simp) with h447 | h447
                                  · linarith only [h0, h215, h413, h423, h425, h427, h429, h447, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p430_1]
                                  · linarith only [h215, h447, hlam]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h215, h423, h427, h429, hc45, hlam, hphi, ht0b, ht5b, p430_1, u0elo3]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, h215, h423, h427, h429, hc45, hlam, hphi, ht0b, ht5b, p430_1, u0elo3]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h216, h427, h429, hc45, hlam, hphi, ht0b, ht5b, p430_1, u0elo3]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  rcases p430_3 (m.d 0 1) (by simp) with h454 | h454
                                  · linarith only [h0, h216, h217, h413, h425, h427, h429, h454, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                  · linarith only [h215, h454, hlam]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h215, hlam, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h409, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h410, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h411, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                              · linarith only [h0, h413, h425, h429, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h215, h413, h424, h428, hlam]
                          · linarith only [h427, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h0, h215, h413, h423, h424, hc25, hlam, hphi, u5elo4]
                    · linarith only [h0, h215, h423, hc15, hlam, hphi, u5elo2]
                · linarith only [h0, h216, h412, hlam]
              · linarith only [h411, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h410, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h409, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h471 | h471
        · rcases m.htr 0 2 5 (by decide) (by decide) with h472 | h472
          · rcases m.htr 0 3 5 (by decide) (by decide) with h473 | h473
            · rcases m.htr 0 4 5 (by decide) (by decide) with h474 | h474
              · rcases m.htr 1 2 3 (by decide) (by decide) with h475 | h475
                · rcases m.htr 1 2 4 (by decide) (by decide) with h476 | h476
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h477 | h477
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h478 | h478
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h479 | h479
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h480 | h480
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h481 | h481
                            · linarith only [h216, h471, h475, h481, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h481, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h216, h480, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h216, h471, h479, hlam]
                      · linarith only [h478, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h477, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h216, h471, h475, h476, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h490 | h490
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h493 | h493
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h494 | h494
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h495 | h495
                              · rcases h0bigk with h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [hlam, p496_0]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h0, hlam, p496_0]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h0, h216, h471, h475, h492, h495, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p496_1]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h0, h475, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p496_1]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h0, h475, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p496_1]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h0, h475, hc01, hc23, hlam, hphi, ht12, p496_1]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [hlam, p496_0]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h216, hlam, p496_1]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h0, h471, h475, h492, h495, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p496_1]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  rcases p496_3 (m.d 0 1) (by simp) with h506 | h506
                                  · linarith only [h0, h506, hlam]
                                  · linarith only [h215, h506, hlam]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h215, h490, h493, h495, hc45, hlam, hphi, ht0b, ht5b, p496_1, u0elo2]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h0, h215, h490, h493, h495, hc45, hlam, hphi, ht0b, ht5b, p496_1, u0elo2]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [hlam, p496_0]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h471, h492, h495, hc45, hlam, hphi, ht0b, ht5b, p496_1, u0elo2]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  rcases p496_3 (m.d 0 1) (by simp) with h513 | h513
                                  · linarith only [h0, h216, h471, h475, h492, h495, h513, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h215, h513, hlam]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h215, h490, h493, h495, hc45, hlam, hphi, ht0b, ht5b, p496_1, u0elo3]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h471, hlam, p496_0]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h216, h471, hlam, p496_1]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [hlam, p496_0]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  rcases p496_3 (m.d 0 1) (by simp) with h520 | h520
                                  · linarith only [h0, h215, h475, h490, h493, h495, h520, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p496_1]
                                  · linarith only [h215, h520, hlam]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h215, hlam, p496_1]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h472, hlam, p496_0]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h473, hlam, p496_0]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [h474, hlam, p496_0]
                                · have p496_0 := h496c.1
                                  have p496_1 := h496c.2.1
                                  have p496_2 := h496c.2.2.1
                                  have p496_3 := h496c.2.2.2
                                  linarith only [hlam, p496_0]
                              · linarith only [h495, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h215, h491, h494, hc24, hlam, hphi, ht45, u5elo0]
                          · linarith only [h0, h475, h493, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h215, h475, h491, h492, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h491, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h490, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h215, h471, h489, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h474, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h473, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h472, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h538 | h538
          · rcases m.htr 0 3 5 (by decide) (by decide) with h539 | h539
            · rcases m.htr 0 4 5 (by decide) (by decide) with h540 | h540
              · rcases m.htr 1 2 3 (by decide) (by decide) with h541 | h541
                · rcases m.htr 1 2 4 (by decide) (by decide) with h542 | h542
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h543 | h543
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h544 | h544
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h546 | h546
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h547 | h547
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h548 | h548
                              · rcases h0bigk with h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [hlam, p549_0]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h0, hlam, p549_0]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h0, h216, hlam, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h0, h471, hlam, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h0, h471, h541, h545, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h471, h541, h545, hc01, hc12, hlam, hphi, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [hlam, p549_0]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h216, hlam, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h471, hlam, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h215, h471, h541, h543, h545, h546, h548, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h215, h216, h541, h543, h546, h548, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h0, h215, h216, h541, h543, h546, h548, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [hlam, p549_0]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h0, h215, h216, h471, h541, h543, h546, h548, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  rcases p549_3 (m.d 0 1) (by simp) with h564 | h564
                                  · linarith only [h0, h216, h564, hlam]
                                  · linarith only [h215, h564, hlam]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h215, h543, h546, h548, hc45, hlam, hphi, ht0b, ht5b, p549_1, u0elo3]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h0, h215, h543, h546, h548, hc45, hlam, hphi, ht0b, ht5b, p549_1, u0elo3]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h0, h215, h216, h471, h541, h543, h545, h546, h548, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [hlam, p549_0]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  rcases p549_3 (m.d 0 1) (by simp) with h571 | h571
                                  · linarith only [h0, h471, h571, hlam]
                                  · linarith only [h215, h571, hlam]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h215, hlam, p549_1]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h538, hlam, p549_0]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h539, hlam, p549_0]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [h540, hlam, p549_0]
                                · have p549_0 := h549c.1
                                  have p549_1 := h549c.2.1
                                  have p549_2 := h549c.2.2.1
                                  have p549_3 := h549c.2.2.2
                                  linarith only [hlam, p549_0]
                              · linarith only [h548, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h215, h471, h544, h547, hlam]
                          · linarith only [h0, h471, h545, h546, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h582 | h582
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h583 | h583
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h584 | h584
                              · rcases h0bigk with h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h216, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h471, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h216, h545, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h216, h545, hc01, hc34, hlam, hphi, ht12, ht23, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h216, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h471, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h215, h216, h543, h545, h582, h584, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h215, h543, h582, h584, hc45, hlam, hphi, ht0b, ht5b, p585_1, u0elo2]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h215, h543, h582, h584, hc45, hlam, hphi, ht0b, ht5b, p585_1, u0elo2]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h215, h216, h471, h543, h545, h582, h584, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  rcases p585_3 (m.d 0 1) (by simp) with h600 | h600
                                  · linarith only [h0, h216, h600, hlam]
                                  · linarith only [h215, h600, hlam]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h215, h543, h582, h584, hc45, hlam, hphi, ht0b, ht5b, p585_1, u0elo3]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h215, h543, h582, h584, hc45, hlam, hphi, ht0b, ht5b, p585_1, u0elo3]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h215, h216, h543, h582, h584, hc45, hlam, hphi, ht0b, ht5b, p585_1, u0elo3]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  rcases p585_3 (m.d 0 1) (by simp) with h607 | h607
                                  · linarith only [h0, h471, h607, hlam]
                                  · linarith only [h215, h607, hlam]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h215, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h538, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h539, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h540, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                              · linarith only [h545, h584, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h0, h215, h216, h544, h545, h583, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h216, h582, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h215, h471, h542, h543, h544, hc25, hlam, hphi, u5elo4]
                    · linarith only [h216, h538, h541, h543, hlam]
                  · linarith only [h0, h216, h541, h542, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h621 | h621
                  · linarith only [h0, h215, h471, h541, h621, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h623 | h623
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h624 | h624
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h625 | h625
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h626 | h626
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h627 | h627
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h628 | h628
                              · rcases h0bigk with h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [hlam, p629_0]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h0, hlam, p629_0]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h0, h621, h625, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p629_1]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h0, h621, h625, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p629_1]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h0, h621, h625, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p629_1]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h0, h621, h625, hc01, hc23, hlam, hphi, ht12, p629_1]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [hlam, p629_0]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h216, hlam, p629_1]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h471, hlam, p629_1]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  rcases p629_3 (m.d 0 1) (by simp) with h639 | h639
                                  · linarith only [h0, h639, hlam]
                                  · linarith only [h215, h639, hlam]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h215, h623, h626, h628, hc45, hlam, hphi, ht0b, ht5b, p629_1, u0elo2]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h0, h215, h623, h626, h628, hc45, hlam, hphi, ht0b, ht5b, p629_1, u0elo2]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [hlam, p629_0]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h0, h215, h471, h623, h626, h628, hc45, hlam, hphi, ht0b, ht5b, p629_1, u0elo2]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  rcases p629_3 (m.d 0 1) (by simp) with h646 | h646
                                  · linarith only [h0, h216, h646, hlam]
                                  · linarith only [h215, h646, hlam]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h215, h623, h626, h628, hc45, hlam, hphi, ht0b, ht5b, p629_1, u0elo3]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h0, h215, h623, h626, h628, hc45, hlam, hphi, ht0b, ht5b, p629_1, u0elo3]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h0, h215, h216, h623, h626, h628, hc45, hlam, hphi, ht0b, ht5b, p629_1, u0elo3]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [hlam, p629_0]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  rcases p629_3 (m.d 0 1) (by simp) with h653 | h653
                                  · linarith only [h0, h471, h653, hlam]
                                  · linarith only [h215, h653, hlam]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h215, hlam, p629_1]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h538, hlam, p629_0]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h539, hlam, p629_0]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [h540, hlam, p629_0]
                                · have p629_0 := h629c.1
                                  have p629_1 := h629c.2.1
                                  have p629_2 := h629c.2.2.1
                                  have p629_3 := h629c.2.2.2
                                  linarith only [hlam, p629_0]
                              · linarith only [h628, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h215, h621, h624, h627, hlam]
                          · linarith only [h0, h621, h625, h626, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h215, h541, h623, h625, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h624, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h215, h623, hc15, hlam, hphi, u5elo2]
              · linarith only [h471, h540, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h539, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h0, h215, h538, hc15, hlam, hphi, u5elo2]
    · linarith only [h215, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT2_M_LI_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h5ehi := hb5.1
  have h2bigk := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h2, h6, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h2, h4, h8, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h2, h6, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h0, h10, h12, h14, h2, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · linarith only [h0, h10, h14, h2, hc23, hc35, hlam, hphi]
                  · linarith only [h10, h11, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h10, h4, h6, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h19 | h19
            · linarith only [h0, h19, h2, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
              · linarith only [h21, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h2, h24, h5, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h0, h19, h26, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                      · linarith only [h0, h1, h2, h21, h23, h28, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h2, h23, h28, hc23, hc35, hlam, hphi]
                · linarith only [h23, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h32 | h32
          · rcases m.htr 0 2 5 (by decide) (by decide) with h33 | h33
            · linarith only [h33, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
              · linarith only [h1, h2, h35, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                · linarith only [h0, h37, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
                    · linarith only [h0, h33, h40, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                      · linarith only [h1, h2, h35, h4, h40, h42, hc02, hc25, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                          · linarith only [h0, h2, h39, h42, h44, h45, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                            · linarith only [h1, h2, h37, h39, h40, h45, h47, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h1, h2, h37, h39, h40, h44, h47, hc34, hc45, hlam, hphi]
                        · linarith only [h0, h39, h4, h44, hlam]
                  · linarith only [h32, h39, h4, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h52 | h52
            · linarith only [h1, h2, h4, h52, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h54 | h54
              · linarith only [h1, h2, h54, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
                · linarith only [h0, h2, h4, h56, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                  · linarith only [h0, h32, h58, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                    · linarith only [h0, h52, h60, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                      · linarith only [h1, h2, h4, h54, h60, h62, hc02, hc25, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                          · linarith only [h0, h2, h62, h65, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h67 | h67
                            · linarith only [h64, h65, h67, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases h2bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h4, h65, hc12, hc35, hlam, hphi, ht23, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h4, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h32, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h52, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h56, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h58, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h60, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h65, hc02, hc35, hlam, hphi, ht23, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h65, hc12, hc35, hlam, hphi, ht23, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h32, h65, hc12, hc35, hlam, hphi, ht23, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h65, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h64, h65, hc12, hc35, hlam, hphi, ht23, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h64, h65, hc12, hc35, hlam, hphi, ht23, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h64, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h67, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                rcases p69_3 (m.d 0 2) (by simp) with h90 | h90
                                · linarith only [h90, hlam, p69_0]
                                · rcases p69_3 (m.d 1 2) (by simp) with h92 | h92
                                  · linarith only [h60, h92, hlam]
                                  · rcases p69_3 (m.d 2 3) (by simp) with h94 | h94
                                    · linarith only [h65, h94, hlam]
                                    · linarith only [h4, h94, hlam]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                rcases p69_3 (m.d 0 2) (by simp) with h97 | h97
                                · linarith only [h52, h97, hlam]
                                · linarith only [h0, h97, hlam]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h64, h67, hc34, hc45, hlam, hphi, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h32, h67, hc12, hc45, hlam, hphi, ht23, ht34, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                          · linarith only [h103, h64, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h105 | h105
                            · rcases h2bigk with h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h4, h64, hc12, hc34, hlam, hphi, ht23, p106_1]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h4, hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h32, hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h52, hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h0, hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h56, hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h58, hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h60, hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h64, hc02, hc34, hlam, hphi, ht23, p106_1]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h64, hc12, hc34, hlam, hphi, ht23, p106_1]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h64, hlam, p106_1]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h103, hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                rcases p106_3 (m.d 0 2) (by simp) with h122 | h122
                                · linarith only [h122, hlam, p106_0]
                                · rcases p106_3 (m.d 1 2) (by simp) with h124 | h124
                                  · linarith only [h124, h58, hlam]
                                  · rcases p106_3 (m.d 2 3) (by simp) with h126 | h126
                                    · linarith only [h126, h64, hlam]
                                    · linarith only [h126, h4, hlam]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                rcases p106_3 (m.d 0 2) (by simp) with h129 | h129
                                · linarith only [h129, h32, hlam]
                                · linarith only [h0, h129, hlam]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h0, h4, hc12, hc24, hlam, hphi, p106_1]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [hlam, p106_0]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p106_1, u5ehi2]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                rcases p106_3 (m.d 0 2) (by simp) with h135 | h135
                                · linarith only [h135, hlam, p106_0]
                                · rcases p106_3 (m.d 1 2) (by simp) with h137 | h137
                                  · linarith only [h137, h60, hlam]
                                  · rcases p106_3 (m.d 2 3) (by simp) with h139 | h139
                                    · linarith only [h103, h139, hlam]
                                    · linarith only [h139, h4, hlam]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                rcases p106_3 (m.d 0 2) (by simp) with h142 | h142
                                · linarith only [h142, h52, hlam]
                                · linarith only [h0, h142, hlam]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h0, h4, hc12, hc25, hlam, hphi, p106_1]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [h105, hlam, p106_1]
                              · have p106_0 := h106c.1
                                have p106_1 := h106c.2.1
                                have p106_2 := h106c.2.2.1
                                have p106_3 := h106c.2.2.2
                                linarith only [hlam, p106_0]
                            · rcases h2bigk with h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h4, hc12, hc23, hlam, hphi, p148_1]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h4, hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h32, hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h52, hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h0, hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h56, hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h58, hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h60, hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h64, hc02, hc34, hlam, hphi, ht23, p148_1]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h64, hc12, hc34, hlam, hphi, ht23, p148_1]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h64, hlam, p148_1]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h103, hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h0, h105, hc12, hc45, hlam, hphi, ht23, ht34, p148_1]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h105, hc12, hc45, hlam, hphi, ht23, ht34, p148_1]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h105, hc23, hc45, hlam, hphi, ht34, p148_1]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h105, hlam, p148_0]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                rcases p148_3 (m.d 0 2) (by simp) with h169 | h169
                                · linarith only [h169, hlam, p148_0]
                                · rcases p148_3 (m.d 1 2) (by simp) with h171 | h171
                                  · linarith only [h171, h60, hlam]
                                  · rcases p148_3 (m.d 2 3) (by simp) with h173 | h173
                                    · linarith only [h103, h173, hlam]
                                    · linarith only [h173, h4, hlam]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                rcases p148_3 (m.d 0 2) (by simp) with h176 | h176
                                · linarith only [h176, h52, hlam]
                                · linarith only [h0, h176, hlam]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h0, h105, h4, hc12, hc45, hlam, hphi, ht23, ht34, p148_1]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [h0, h105, h32, hc12, hc45, hlam, hphi, ht23, ht34, p148_1]
                              · have p148_0 := h148c.1
                                have p148_1 := h148c.2.1
                                have p148_2 := h148c.2.2.1
                                have p148_3 := h148c.2.2.2
                                linarith only [hlam, p148_0]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h182 | h182
      · linarith only [h182, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h184 | h184
        · linarith only [h0, h1, h184, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h186 | h186
          · rcases m.htr 0 2 5 (by decide) (by decide) with h187 | h187
            · linarith only [h0, h187, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h189 | h189
              · linarith only [h189, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                · linarith only [h0, h184, h191, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
                    · linarith only [h0, h187, h194, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h196 | h196
                      · linarith only [h0, h1, h189, h193, h196, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h193, h196, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h184, h186, h193, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h200 | h200
            · linarith only [h0, h1, h200, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h202 | h202
              · linarith only [h202, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
                · linarith only [h0, h1, h202, h204, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h206 | h206
                  · linarith only [h0, h1, h186, h202, h206, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h208 | h208
                    · linarith only [h0, h200, h208, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                      · linarith only [h0, h1, h202, h204, h210, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h210, hc12, hc35, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h213 | h213
    · rcases m.htr 0 1 5 (by decide) (by decide) with h214 | h214
      · linarith only [h214, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h216 | h216
        · rcases m.htr 0 2 4 (by decide) (by decide) with h217 | h217
          · rcases m.htr 0 2 5 (by decide) (by decide) with h218 | h218
            · linarith only [h218, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h220 | h220
              · linarith only [h0, h213, h218, h220, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                      · linarith only [h0, h213, h218, h220, h224, h225, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                        · linarith only [h0, h213, h218, h222, h224, h227, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h229 | h229
                          · linarith only [h0, h213, h218, h222, h224, h225, h229, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h231 | h231
                            · linarith only [h217, h218, h224, h231, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases h2bigk with h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h0, hlam, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h218, h224, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h218, h224, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h218, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                rcases p233_3 (m.d 0 2) (by simp) with h239 | h239
                                · linarith only [h0, h239, hlam]
                                · rcases p233_3 (m.d 1 2) (by simp) with h241 | h241
                                  · rcases p233_3 (m.d 2 3) (by simp) with h242 | h242
                                    · linarith only [h222, h242, hlam]
                                    · rcases p233_3 (m.d 2 4) (by simp) with h244 | h244
                                      · linarith only [h223, h244, hlam]
                                      · rcases p233_3 (m.d 2 5) (by simp) with h246 | h246
                                        · linarith only [h224, h246, hlam]
                                        · linarith only [h218, h246, hlam]
                                  · linarith only [h0, h241, hlam]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h216, h218, h224, hlam, p233_2]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h217, h218, h224, hlam, p233_2]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h0, h218, hc01, hc12, hlam, hphi, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h216, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h222, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h227, hlam, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h229, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h217, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h223, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h217, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1, u0elo1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h231, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h217, h231, hc24, hc45, hlam, hphi, p233_1]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [h224, hlam, p233_0]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                rcases p233_3 (m.d 0 2) (by simp) with h266 | h266
                                · linarith only [h218, h266, hlam]
                                · linarith only [h216, h266, hlam]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                rcases p233_3 (m.d 0 2) (by simp) with h269 | h269
                                · linarith only [h218, h269, hlam]
                                · linarith only [h217, h269, hlam]
                              · have p233_0 := h233c.1
                                have p233_1 := h233c.2.1
                                have p233_2 := h233c.2.2.1
                                have p233_3 := h233c.2.2.2
                                linarith only [hlam, p233_0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h273 | h273
                      · linarith only [h213, h273, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h275 | h275
                        · linarith only [h0, h213, h222, h224, h275, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                          · linarith only [h0, h213, h222, h224, h273, h277, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                          · linarith only [h0, h213, h222, h224, h277, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h213, h217, h222, h223, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h216, h222, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h282 | h282
            · linarith only [h217, h282, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h284 | h284
              · linarith only [h0, h213, h217, h284, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h286 | h286
                · rcases m.htr 1 2 4 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
                      · linarith only [h0, h213, h217, h284, h287, h289, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                        · linarith only [h0, h213, h217, h286, h287, h291, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h293 | h293
                          · linarith only [h0, h213, h217, h286, h287, h289, h293, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h295 | h295
                            · linarith only [h287, h295, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h0, h213, h217, h295, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h213, h217, h286, h287, h288, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h299 | h299
                    · linarith only [h287, h299, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h301 | h301
                      · linarith only [h213, h301, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                        · linarith only [h0, h213, h286, h287, h303, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h213, h286, h287, h303, hc23, hc34, hlam, hphi]
                · linarith only [h0, h216, h286, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h213, h216, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h308 | h308
      · linarith only [h308, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h310 | h310
        · rcases m.htr 0 2 4 (by decide) (by decide) with h311 | h311
          · rcases m.htr 0 2 5 (by decide) (by decide) with h312 | h312
            · linarith only [h312, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h314 | h314
              · linarith only [h310, h312, h314, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
                · rcases m.htr 1 2 4 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h319 | h319
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                        · linarith only [h310, h312, h318, h320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
                          · linarith only [h213, h311, h312, h314, h318, h320, h322, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h324 | h324
                            · linarith only [h311, h312, h316, h319, h322, h324, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases h2bigk with h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h0, hlam, p326_1]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h312, h316, h319, h322, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p326_1]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h312, h316, h319, h322, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p326_1]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h312, hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                rcases p326_3 (m.d 0 2) (by simp) with h332 | h332
                                · linarith only [h0, h332, hlam]
                                · rcases p326_3 (m.d 1 2) (by simp) with h334 | h334
                                  · rcases p326_3 (m.d 2 3) (by simp) with h335 | h335
                                    · linarith only [h316, h335, hlam]
                                    · rcases p326_3 (m.d 2 4) (by simp) with h337 | h337
                                      · linarith only [h317, h337, hlam]
                                      · rcases p326_3 (m.d 2 5) (by simp) with h339 | h339
                                        · linarith only [h318, h339, hlam]
                                        · linarith only [h312, h339, hlam]
                                  · linarith only [h0, h334, hlam]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h310, h312, h316, h319, h322, hlam, p326_2]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h311, h312, h316, h319, h322, hlam, p326_2]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h311, h312, h320, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p326_1]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h310, hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h316, hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h320, hlam, p326_1]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h322, hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h311, hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h317, hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h311, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p326_1, u0elo1]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h324, hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h311, h324, hc24, hc45, hlam, hphi, p326_1]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [h318, hlam, p326_0]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                rcases p326_3 (m.d 0 2) (by simp) with h359 | h359
                                · linarith only [h312, h359, hlam]
                                · linarith only [h310, h359, hlam]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                rcases p326_3 (m.d 0 2) (by simp) with h362 | h362
                                · linarith only [h312, h362, hlam]
                                · linarith only [h311, h362, hlam]
                              · have p326_0 := h326c.1
                                have p326_1 := h326c.2.1
                                have p326_2 := h326c.2.2.1
                                have p326_3 := h326c.2.2.2
                                linarith only [hlam, p326_0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h366 | h366
                        · linarith only [h310, h312, h318, h366, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h368 | h368
                          · linarith only [h311, h312, h318, h319, h366, h368, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h370 | h370
                            · linarith only [h311, h312, h318, h370, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases h2bigk with h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h0, hlam, p372_1]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h312, h318, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p372_1]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h312, h318, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p372_1]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h312, hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                rcases p372_3 (m.d 0 2) (by simp) with h378 | h378
                                · linarith only [h0, h378, hlam]
                                · rcases p372_3 (m.d 1 2) (by simp) with h380 | h380
                                  · rcases p372_3 (m.d 2 3) (by simp) with h381 | h381
                                    · linarith only [h316, h381, hlam]
                                    · rcases p372_3 (m.d 2 4) (by simp) with h383 | h383
                                      · linarith only [h317, h383, hlam]
                                      · rcases p372_3 (m.d 2 5) (by simp) with h385 | h385
                                        · linarith only [h318, h385, hlam]
                                        · linarith only [h312, h385, hlam]
                                  · linarith only [h0, h380, hlam]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h310, h312, h318, hlam, p372_2]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h311, h312, h318, hlam, p372_2]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h311, h312, h366, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p372_1]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h310, hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h316, hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h366, hlam, p372_1]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h368, hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h311, hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h317, hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h311, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p372_1, u0elo1]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h370, hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h311, h370, hc24, hc45, hlam, hphi, p372_1]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [h318, hlam, p372_0]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                rcases p372_3 (m.d 0 2) (by simp) with h405 | h405
                                · linarith only [h312, h405, hlam]
                                · linarith only [h310, h405, hlam]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                rcases p372_3 (m.d 0 2) (by simp) with h408 | h408
                                · linarith only [h312, h408, hlam]
                                · linarith only [h311, h408, hlam]
                              · have p372_0 := h372c.1
                                have p372_1 := h372c.2.1
                                have p372_2 := h372c.2.2.1
                                have p372_3 := h372c.2.2.2
                                linarith only [hlam, p372_0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h412 | h412
                      · linarith only [h314, h316, h318, h412, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h414 | h414
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h415 | h415
                          · linarith only [h310, h412, h415, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h417 | h417
                            · linarith only [h0, h310, h318, h414, h415, h417, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h0, h310, h318, h414, h417, hc34, hc45, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
                          · linarith only [h311, h414, h420, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h422 | h422
                            · linarith only [h0, h311, h318, h420, h422, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases h2bigk with h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h0, hlam, p424_1]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h0, h318, h422, hc23, hc45, hlam, hphi, ht34, p424_1]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h0, h318, h422, hc24, hc45, hlam, hphi, p424_1]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h312, hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h318, h422, hc02, hc45, hlam, hphi, ht23, ht34, p424_1]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h318, h422, hc23, hc45, hlam, hphi, ht34, p424_1]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h318, h422, hc24, hc45, hlam, hphi, p424_1]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h318, hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h310, hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h316, hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h414, hlam, p424_1]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h420, hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h311, hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h317, hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h311, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p424_1, u0elo1]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h422, hlam, p424_0]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h311, h422, hc24, hc45, hlam, hphi, p424_1]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [h0, h422, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p424_1]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                rcases p424_3 (m.d 0 2) (by simp) with h447 | h447
                                · linarith only [h312, h447, hlam]
                                · linarith only [h310, h447, hlam]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                rcases p424_3 (m.d 0 2) (by simp) with h450 | h450
                                · linarith only [h312, h450, hlam]
                                · linarith only [h311, h450, hlam]
                              · have p424_0 := h424c.1
                                have p424_1 := h424c.2.1
                                have p424_2 := h424c.2.2.1
                                have p424_3 := h424c.2.2.2
                                linarith only [hlam, p424_0]
                  · linarith only [h213, h311, h316, h317, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h310, h316, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h456 | h456
            · linarith only [h456, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h458 | h458
              · linarith only [h458, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h460 | h460
                · rcases m.htr 1 2 4 (by decide) (by decide) with h461 | h461
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h462 | h462
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h463 | h463
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                        · linarith only [h310, h311, h461, h464, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h466 | h466
                          · linarith only [h310, h311, h458, h461, h466, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h468 | h468
                            · linarith only [h461, h468, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h310, h311, h468, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h471 | h471
                        · linarith only [h310, h311, h461, h471, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h473 | h473
                          · linarith only [h310, h311, h461, h463, h473, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h475 | h475
                            · linarith only [h461, h475, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h310, h311, h475, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h310, h311, h461, h462, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h479 | h479
                    · linarith only [h461, h479, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h481 | h481
                      · linarith only [h458, h460, h461, h481, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                        · linarith only [h0, h310, h456, h461, h483, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h485 | h485
                          · linarith only [h213, h310, h481, h485, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
                            · rcases h2bigk with h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h0, hlam, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h0, h479, h483, h487, hc23, hc34, hlam, hphi, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h311, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h456, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h479, h483, h487, hc02, hc34, hlam, hphi, ht23, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h479, h483, h487, hc23, hc34, hlam, hphi, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h461, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h479, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h310, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h460, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h483, hlam, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h485, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h310, h483, hc23, hc34, hlam, hphi, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h0, h483, hc01, hc34, hlam, hphi, ht12, ht23, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 2) (by simp) with h506 | h506
                                · linarith only [h311, h506, hlam]
                                · linarith only [h310, h506, hlam]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h483, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p488_1, u5ehi2]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h310, h485, hc23, hc35, hlam, hphi, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h213, h460, h485, hc01, hc35, hlam, hphi, ht12, ht23, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 2) (by simp) with h513 | h513
                                · linarith only [h456, h513, hlam]
                                · linarith only [h310, h513, hlam]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h487, hlam, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                            · linarith only [h310, h311, h487, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h310, h460, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h520 | h520
          · rcases m.htr 0 2 5 (by decide) (by decide) with h521 | h521
            · linarith only [h521, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h523 | h523
              · linarith only [h523, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h525 | h525
                · rcases m.htr 1 2 4 (by decide) (by decide) with h526 | h526
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h527 | h527
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h528 | h528
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h529 | h529
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h530 | h530
                          · linarith only [h0, h310, h523, h525, h530, hc01, hc12, hlam, hphi]
                          · linarith only [h310, h520, h528, h529, h530, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h310, h520, h529, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h534 | h534
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h535 | h535
                          · linarith only [h213, h528, h535, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h537 | h537
                            · linarith only [h520, h537, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases h2bigk with h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h0, hlam, p539_1]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h310, hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h310, h525, h528, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p539_1]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h521, hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                rcases p539_3 (m.d 0 2) (by simp) with h545 | h545
                                · linarith only [h0, h545, hlam]
                                · rcases p539_3 (m.d 1 2) (by simp) with h547 | h547
                                  · rcases p539_3 (m.d 2 3) (by simp) with h548 | h548
                                    · linarith only [h525, h548, hlam]
                                    · linarith only [h310, h548, hlam]
                                  · linarith only [h0, h547, hlam]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h0, h310, hc01, hc12, hlam, hphi, p539_1]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h520, h521, h527, hlam, p539_2]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p539_1, u5ehi2]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h520, h525, h534, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p539_1]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h525, hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                rcases p539_3 (m.d 0 2) (by simp) with h559 | h559
                                · linarith only [h310, h559, hlam]
                                · linarith only [h520, h559, hlam]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h535, hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h520, hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h526, hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h534, hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h537, hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h520, h534, h537, hc34, hc45, hlam, hphi, p539_1]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h527, hlam, p539_0]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [h310, h520, h527, h534, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p539_1]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                rcases p539_3 (m.d 0 2) (by simp) with h571 | h571
                                · linarith only [h521, h571, hlam]
                                · linarith only [h520, h571, hlam]
                              · have p539_0 := h539c.1
                                have p539_1 := h539c.2.1
                                have p539_2 := h539c.2.2.1
                                have p539_3 := h539c.2.2.2
                                linarith only [hlam, p539_0]
                        · linarith only [h310, h520, h534, hlam]
                    · linarith only [h310, h525, h527, hc02, hc25, hlam, hphi]
                  · linarith only [h310, h520, h525, h526, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h578 | h578
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h579 | h579
                    · linarith only [h525, h579, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h581 | h581
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h582 | h582
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h583 | h583
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h584 | h584
                            · linarith only [h520, h584, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases h2bigk with h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h0, hlam, p586_1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h310, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h310, h523, h525, h581, h582, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p586_1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h521, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h579, h584, hc02, hc45, hlam, hphi, ht23, ht34, p586_1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h525, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h579, h582, h584, hc34, hc45, hlam, hphi, p586_1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h579, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                rcases p586_3 (m.d 0 2) (by simp) with h597 | h597
                                · linarith only [h597, hlam, p586_0]
                                · rcases p586_3 (m.d 1 2) (by simp) with h599 | h599
                                  · linarith only [h525, h599, hlam]
                                  · linarith only [h0, h599, hlam]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p586_1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h310, h520, h523, h525, h581, hlam, p586_2]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h579, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p586_1, u5ehi1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h520, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h578, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h582, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h584, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h520, h582, h584, hc34, hc45, hlam, hphi, p586_1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p586_1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h583, hlam, p586_1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                rcases p586_3 (m.d 0 2) (by simp) with h614 | h614
                                · linarith only [h521, h614, hlam]
                                · linarith only [h520, h614, hlam]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hlam, p586_0]
                          · linarith only [h525, h581, h583, hlam]
                        · linarith only [h310, h523, h525, h581, h582, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h620 | h620
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h621 | h621
                          · linarith only [h213, h581, h621, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h525, h621, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h525, h620, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h520, h578, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h626 | h626
            · linarith only [h310, h626, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h628 | h628
              · linarith only [h628, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
                · rcases m.htr 1 2 4 (by decide) (by decide) with h631 | h631
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h632 | h632
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h633 | h633
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h635 | h635
                          · linarith only [h630, h635, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h520, h630, h633, h634, h635, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h638 | h638
                          · linarith only [h628, h634, h638, hc03, hc34, hlam, hphi]
                          · linarith only [h0, h310, h630, h633, h638, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h641 | h641
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h642 | h642
                          · linarith only [h213, h633, h642, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h644 | h644
                            · linarith only [h630, h633, h641, h644, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases h2bigk with h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, hlam, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h310, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h520, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h626, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                rcases p646_3 (m.d 0 2) (by simp) with h652 | h652
                                · linarith only [h0, h652, hlam]
                                · rcases p646_3 (m.d 1 2) (by simp) with h654 | h654
                                  · rcases p646_3 (m.d 2 3) (by simp) with h655 | h655
                                    · linarith only [h630, h655, hlam]
                                    · linarith only [h310, h655, hlam]
                                  · linarith only [h0, h654, hlam]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h310, hc01, hc12, hlam, hphi, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h520, hc01, hc12, hlam, hphi, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h626, hc12, hlam, hphi, ht01, ht0b, ht5b, p646_1, u5ehi0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h630, hc01, hc12, hlam, hphi, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h630, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h520, h630, h633, hc01, hc35, hlam, hphi, ht12, ht23, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h642, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h644, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h631, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h641, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h644, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h632, hc01, hc12, hlam, hphi, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h632, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h632, h641, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h520, h632, hc01, hc12, hlam, hphi, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h678 | h678
                          · linarith only [h633, h641, h678, hc13, hc34, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h680 | h680
                            · linarith only [h631, h680, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases h2bigk with h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h0, hlam, p682_1]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h310, hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h520, hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h626, hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                rcases p682_3 (m.d 0 2) (by simp) with h688 | h688
                                · linarith only [h0, h688, hlam]
                                · rcases p682_3 (m.d 1 2) (by simp) with h690 | h690
                                  · rcases p682_3 (m.d 2 3) (by simp) with h691 | h691
                                    · linarith only [h630, h691, hlam]
                                    · linarith only [h310, h691, hlam]
                                  · linarith only [h0, h690, hlam]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h0, h310, hc01, hc12, hlam, hphi, p682_1]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h0, h520, hc01, hc12, hlam, hphi, p682_1]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p682_1, u5ehi2]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h0, h641, hc01, hc34, hlam, hphi, ht12, ht23, p682_1]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h630, hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h641, hlam, p682_1]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h678, hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h0, h631, hc01, hc12, hlam, hphi, p682_1]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h631, hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h0, h310, h631, hc01, hc12, hlam, hphi, p682_1]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h680, hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h0, h632, hc01, hc12, hlam, hphi, p682_1]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h632, hlam, p682_0]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h0, h310, h632, hc01, hc12, hlam, hphi, p682_1]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [h0, h520, h632, hc01, hc12, hlam, hphi, p682_1]
                              · have p682_0 := h682c.1
                                have p682_1 := h682c.2.1
                                have p682_2 := h682c.2.2.1
                                have p682_3 := h682c.2.2.2
                                linarith only [hlam, p682_0]
                    · linarith only [h0, h310, h630, h632, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h310, h630, h631, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h716 | h716
                  · linarith only [h0, h520, h630, h716, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h718 | h718
                    · linarith only [h716, h718, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h720 | h720
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h721 | h721
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h722 | h722
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h723 | h723
                            · rcases h2bigk with h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h0, hlam, p724_1]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h310, hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h520, hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h626, hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h0, h718, h721, h723, hc01, hc23, hlam, hphi, ht12, p724_1]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h630, hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h716, hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h718, hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                rcases p724_3 (m.d 0 2) (by simp) with h735 | h735
                                · linarith only [h735, hlam, p724_0]
                                · rcases p724_3 (m.d 1 2) (by simp) with h737 | h737
                                  · linarith only [h630, h737, hlam]
                                  · linarith only [h0, h737, hlam]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p724_1]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h723, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p724_1, u5ehi2]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h0, h718, hc01, hc23, hlam, hphi, ht12, p724_1]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                rcases p724_3 (m.d 0 2) (by simp) with h744 | h744
                                · linarith only [h744, hlam, p724_0]
                                · rcases p724_3 (m.d 1 2) (by simp) with h746 | h746
                                  · linarith only [h716, h746, hlam]
                                  · linarith only [h0, h746, hlam]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h0, hc01, hc24, hlam, hphi, ht12, p724_1]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h721, hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [hlam, p724_0]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h0, h718, h721, hc01, hc23, hlam, hphi, ht12, p724_1]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                rcases p724_3 (m.d 0 2) (by simp) with h753 | h753
                                · linarith only [h753, hlam, p724_0]
                                · rcases p724_3 (m.d 1 2) (by simp) with h755 | h755
                                  · linarith only [h718, h755, hlam]
                                  · linarith only [h0, h755, hlam]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p724_1]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h722, hlam, p724_1]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [h723, hlam, p724_1]
                              · have p724_0 := h724c.1
                                have p724_1 := h724c.2.1
                                have p724_2 := h724c.2.2.1
                                have p724_3 := h724c.2.2.2
                                linarith only [hlam, p724_0]
                            · linarith only [h0, h716, h723, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h630, h722, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h628, h630, h720, h721, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h766 | h766
                          · linarith only [h213, h720, h766, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h630, h766, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h630, h765, hc01, hc34, hlam, hphi, ht12, ht23]

theorem n7l_sBT2_M_LI_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 5) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 5) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · rcases m.htr 0 1 5 (by decide) (by decide) with h12 | h12
              · linarith only [h12, hlam, p0_0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h14 | h14
                · rcases m.htr 0 2 4 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h12, h16, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1]
                    · linarith only [h14, h16, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h14, h15, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h20 | h20
                  · linarith only [h14, h20, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h14, h22, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h22, h9, hc25, hlam, hphi, p0_1, u2ehi0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h25 | h25
              · linarith only [h25, hlam, p0_0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h27 | h27
                · rcases m.htr 0 2 4 (by decide) (by decide) with h28 | h28
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h29 | h29
                    · linarith only [h29, h9, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h27, h29, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h27, h28, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h27, h33, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h27, h35, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h35, h9, hc25, hlam, hphi, p0_1, u2ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · rcases m.htr 0 1 5 (by decide) (by decide) with h39 | h39
              · linarith only [h39, hlam, p0_0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h41 | h41
                · rcases m.htr 0 2 4 (by decide) (by decide) with h42 | h42
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h43 | h43
                    · linarith only [h43, h9, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h41, h43, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h41, h42, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h47 | h47
                  · linarith only [h41, h47, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h41, h49, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h49, h9, hc25, hlam, hphi, p0_1, u2ehi0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h52 | h52
              · linarith only [h52, hlam, p0_0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h54 | h54
                · rcases m.htr 0 2 4 (by decide) (by decide) with h55 | h55
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h56 | h56
                    · linarith only [h56, h9, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h54, h56, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h54, h55, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h60 | h60
                  · linarith only [h54, h60, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h62 | h62
                    · linarith only [h54, h62, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h62, h9, hc25, hlam, hphi, p0_1, u2ehi0]
        · rcases p0_3 (m.d 3 5) (by simp) with h65 | h65
          · linarith only [h65, h9, hc35, hlam, hphi, ht23, p0_1, u2ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h67 | h67
            · linarith only [h67, h9, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h69 | h69
              · linarith only [h69, hlam, p0_0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h71 | h71
                · rcases m.htr 0 2 4 (by decide) (by decide) with h72 | h72
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h73 | h73
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h75 | h75
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h80 | h80
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                                        · linarith only [h71, h83, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                        · linarith only [h75, h77, h79, h81, h82, h83, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                                      · linarith only [h74, h82, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                                    · linarith only [h76, h81, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi0]
                                  · linarith only [h75, h77, h80, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                                · linarith only [h71, h74, h77, h79, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                              · linarith only [h73, h78, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
                            · linarith only [h71, h77, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                          · linarith only [h67, h76, hlam]
                        · linarith only [h65, h75, hlam]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h96 | h96
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                                · linarith only [h74, h94, h98, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                                  · linarith only [h100, h98, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi0]
                                  · linarith only [h100, h74, h94, hc13, hc34, hlam, hphi]
                              · linarith only [h73, h97, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
                            · linarith only [h71, h96, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                          · linarith only [h67, h95, hlam]
                        · linarith only [h65, h94, hlam]
                    · linarith only [h73, h9, hlam]
                  · linarith only [h71, h72, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h109 | h109
                  · linarith only [h109, h71, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h111 | h111
                    · linarith only [h111, h71, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h111, h9, hlam]
      · linarith only [h8, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h116 | h116
    · linarith only [h116, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u2ehi4]
    · rcases p0_3 (m.d 1 5) (by simp) with h118 | h118
      · rcases p0_3 (m.d 2 5) (by simp) with h119 | h119
        · linarith only [h119, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h121 | h121
          · linarith only [h121, hc35, hlam, hphi, ht23, p0_1, u2ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h123 | h123
            · linarith only [h123, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h125 | h125
              · linarith only [h125, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u2ehi4]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h127 | h127
                · rcases m.htr 0 2 4 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h129 | h129
                    · linarith only [h116, h129, hlam]
                    · linarith only [h129, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
                  · linarith only [h127, h128, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h133 | h133
                  · linarith only [h127, h133, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h135 | h135
                    · linarith only [h116, h135, hlam]
                    · linarith only [h135, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
      · linarith only [h118, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h139 | h139
    · linarith only [h139, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · rcases p0_3 (m.d 1 5) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 5) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 5) (by simp) with h143 | h143
          · linarith only [h143, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h145 | h145
            · rcases m.htr 0 1 5 (by decide) (by decide) with h146 | h146
              · linarith only [h146, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi3]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h148 | h148
                · rcases m.htr 0 2 4 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h150 | h150
                    · linarith only [h142, h150, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                    · linarith only [h148, h150, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h148, h149, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h154 | h154
                  · linarith only [h148, h154, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h156 | h156
                    · linarith only [h148, h156, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h139, h145, h156, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h159 | h159
              · linarith only [h139, h159, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h161 | h161
                · rcases m.htr 0 2 4 (by decide) (by decide) with h162 | h162
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h163 | h163
                    · linarith only [h142, h163, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                    · linarith only [h161, h163, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h161, h162, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h167 | h167
                  · linarith only [h161, h167, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h169 | h169
                    · linarith only [h161, h169, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h139, h142, h169, hc25, hlam, hphi, p0_1, u2ehi0]
        · rcases p0_3 (m.d 3 5) (by simp) with h172 | h172
          · linarith only [h172, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h174 | h174
            · linarith only [h142, h174, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h176 | h176
              · linarith only [h142, h176, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u2ehi4]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h178 | h178
                · rcases m.htr 0 2 4 (by decide) (by decide) with h179 | h179
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h180 | h180
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h181 | h181
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h182 | h182
                        · linarith only [h139, h182, hlam]
                        · linarith only [h181, h182, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h185 | h185
                        · linarith only [h139, h185, hlam]
                        · linarith only [h178, h185, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                    · linarith only [h178, h180, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h178, h179, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h190 | h190
                  · linarith only [h178, h190, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h192 | h192
                    · linarith only [h178, h192, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h142, h192, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
      · linarith only [h141, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h196 | h196
    · linarith only [h196, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
    · rcases p0_3 (m.d 1 5) (by simp) with h198 | h198
      · rcases p0_3 (m.d 2 5) (by simp) with h199 | h199
        · rcases p0_3 (m.d 3 5) (by simp) with h200 | h200
          · rcases p0_3 (m.d 4 5) (by simp) with h201 | h201
            · linarith only [h201, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h203 | h203
              · linarith only [h203, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi4]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h205 | h205
                · rcases m.htr 0 2 4 (by decide) (by decide) with h206 | h206
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h207 | h207
                    · linarith only [h199, h207, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi4]
                    · linarith only [h205, h207, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h205, h206, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h211 | h211
                  · linarith only [h205, h211, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h213 | h213
                    · linarith only [h205, h213, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h196, h200, h213, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h216 | h216
            · linarith only [h216, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h218 | h218
              · linarith only [h196, h218, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h220 | h220
                · rcases m.htr 0 2 4 (by decide) (by decide) with h221 | h221
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h222 | h222
                    · linarith only [h196, h199, h222, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h220, h222, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h220, h221, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h226 | h226
                  · linarith only [h220, h226, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h228 | h228
                    · linarith only [h220, h228, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h196, h199, h228, hc25, hlam, hphi, p0_1, u2ehi0]
        · rcases p0_3 (m.d 3 5) (by simp) with h231 | h231
          · linarith only [h199, h231, hc35, hlam, hphi, ht23, p0_1, u2ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h233 | h233
            · linarith only [h233, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h235 | h235
              · linarith only [h199, h235, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u2ehi4]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h237 | h237
                · rcases m.htr 0 2 4 (by decide) (by decide) with h238 | h238
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h239 | h239
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h240 | h240
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h241 | h241
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h242 | h242
                          · linarith only [h196, h242, hlam]
                          · linarith only [h238, h242, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
                        · linarith only [h231, h237, h241, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h246 | h246
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h247 | h247
                          · linarith only [h196, h247, hlam]
                          · linarith only [h240, h246, h247, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi3]
                        · linarith only [h231, h237, h246, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                    · linarith only [h199, h239, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
                  · linarith only [h237, h238, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h253 | h253
                  · linarith only [h237, h253, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h255 | h255
                    · linarith only [h237, h255, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h199, h255, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
      · linarith only [h198, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h259 | h259
    · linarith only [h259, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h261 | h261
      · rcases p0_3 (m.d 2 5) (by simp) with h262 | h262
        · rcases p0_3 (m.d 3 5) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · rcases m.htr 0 1 5 (by decide) (by decide) with h265 | h265
              · linarith only [h261, h265, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h267 | h267
                · rcases m.htr 0 2 4 (by decide) (by decide) with h268 | h268
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h269 | h269
                    · linarith only [h269, hlam, p0_0]
                    · linarith only [h267, h269, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h267, h268, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h273 | h273
                  · linarith only [h267, h273, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h275 | h275
                    · linarith only [h275, hlam, p0_0]
                    · linarith only [h264, h275, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h278 | h278
              · linarith only [h261, h278, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h280 | h280
                · rcases m.htr 0 2 4 (by decide) (by decide) with h281 | h281
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h282 | h282
                    · linarith only [h282, hlam, p0_0]
                    · linarith only [h280, h282, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h280, h281, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h286 | h286
                  · linarith only [h280, h286, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h288 | h288
                    · linarith only [h288, hlam, p0_0]
                    · linarith only [h263, h288, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h291 | h291
            · rcases m.htr 0 1 5 (by decide) (by decide) with h292 | h292
              · linarith only [h261, h292, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h294 | h294
                · rcases m.htr 0 2 4 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h296 | h296
                    · linarith only [h296, hlam, p0_0]
                    · linarith only [h294, h296, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h294, h295, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h300 | h300
                  · linarith only [h294, h300, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h302 | h302
                    · linarith only [h302, hlam, p0_0]
                    · linarith only [h291, h302, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h305 | h305
              · linarith only [h261, h305, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h307 | h307
                · rcases m.htr 0 2 4 (by decide) (by decide) with h308 | h308
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h309 | h309
                    · linarith only [h309, hlam, p0_0]
                    · linarith only [h307, h309, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h307, h308, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h313 | h313
                  · linarith only [h307, h313, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h315 | h315
                    · linarith only [h315, hlam, p0_0]
                    · linarith only [h315, hc25, hlam, hphi, p0_1, u2ehi0]
        · linarith only [h262, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h319 | h319
        · rcases p0_3 (m.d 3 5) (by simp) with h320 | h320
          · rcases p0_3 (m.d 4 5) (by simp) with h321 | h321
            · rcases m.htr 0 1 5 (by decide) (by decide) with h322 | h322
              · rcases m.htr 0 2 3 (by decide) (by decide) with h323 | h323
                · rcases m.htr 0 2 4 (by decide) (by decide) with h324 | h324
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h325 | h325
                    · linarith only [h325, hlam, p0_0]
                    · linarith only [h321, h323, h325, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h323, h324, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h329 | h329
                  · linarith only [h323, h329, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h331 | h331
                    · linarith only [h331, hlam, p0_0]
                    · linarith only [h321, h331, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
              · linarith only [h261, h322, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h335 | h335
              · rcases m.htr 0 2 3 (by decide) (by decide) with h336 | h336
                · rcases m.htr 0 2 4 (by decide) (by decide) with h337 | h337
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h338 | h338
                    · linarith only [h338, hlam, p0_0]
                    · linarith only [h336, h338, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h336, h337, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h342 | h342
                  · linarith only [h336, h342, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h344 | h344
                    · linarith only [h344, hlam, p0_0]
                    · linarith only [h320, h344, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
              · linarith only [h261, h335, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h348 | h348
            · rcases m.htr 0 1 5 (by decide) (by decide) with h349 | h349
              · rcases m.htr 0 2 3 (by decide) (by decide) with h350 | h350
                · rcases m.htr 0 2 4 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h352 | h352
                    · linarith only [h352, hlam, p0_0]
                    · linarith only [h348, h350, h352, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h350, h351, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h356 | h356
                  · linarith only [h350, h356, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h358 | h358
                    · linarith only [h358, hlam, p0_0]
                    · linarith only [h348, h358, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
              · linarith only [h261, h349, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h362 | h362
              · rcases m.htr 0 2 3 (by decide) (by decide) with h363 | h363
                · rcases m.htr 0 2 4 (by decide) (by decide) with h364 | h364
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h365 | h365
                    · linarith only [h365, hlam, p0_0]
                    · linarith only [h363, h365, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h363, h364, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h369 | h369
                  · linarith only [h363, h369, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h371 | h371
                    · linarith only [h371, hlam, p0_0]
                    · linarith only [h371, hc25, hlam, hphi, p0_1, u2ehi0]
              · linarith only [h261, h362, hlam]
        · linarith only [h319, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h376 | h376
    · linarith only [h376, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · rcases p0_3 (m.d 1 5) (by simp) with h378 | h378
      · linarith only [h378, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h380 | h380
        · rcases p0_3 (m.d 3 5) (by simp) with h381 | h381
          · rcases p0_3 (m.d 4 5) (by simp) with h382 | h382
            · rcases m.htr 0 1 5 (by decide) (by decide) with h383 | h383
              · linarith only [h376, h383, hlam]
              · linarith only [h383, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h386 | h386
              · linarith only [h376, h386, hlam]
              · linarith only [h381, h386, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h389 | h389
            · rcases m.htr 0 1 5 (by decide) (by decide) with h390 | h390
              · linarith only [h376, h390, hlam]
              · linarith only [h389, h390, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h393 | h393
              · linarith only [h376, h393, hlam]
              · linarith only [h393, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h380, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h398 | h398
    · linarith only [h398, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · rcases p0_3 (m.d 1 5) (by simp) with h400 | h400
      · rcases p0_3 (m.d 2 5) (by simp) with h401 | h401
        · rcases p0_3 (m.d 3 5) (by simp) with h402 | h402
          · linarith only [h402, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h404 | h404
            · rcases m.htr 0 1 5 (by decide) (by decide) with h405 | h405
              · linarith only [h400, h405, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi3]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h407 | h407
                · rcases m.htr 0 2 4 (by decide) (by decide) with h408 | h408
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h409 | h409
                    · linarith only [h409, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                    · linarith only [h404, h407, h409, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h407, h408, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h413 | h413
                  · linarith only [h407, h413, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h415 | h415
                    · linarith only [h407, h415, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h398, h404, h415, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h418 | h418
              · linarith only [h398, h400, h418, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h420 | h420
                · rcases m.htr 0 2 4 (by decide) (by decide) with h421 | h421
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h422 | h422
                    · linarith only [h398, h422, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h420, h422, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h420, h421, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h426 | h426
                  · linarith only [h420, h426, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h428 | h428
                    · linarith only [h420, h428, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h398, h428, hc25, hlam, hphi, p0_1, u2ehi0]
        · linarith only [h401, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h432 | h432
        · rcases p0_3 (m.d 3 5) (by simp) with h433 | h433
          · linarith only [h433, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h435 | h435
            · rcases m.htr 0 1 5 (by decide) (by decide) with h436 | h436
              · rcases m.htr 0 2 3 (by decide) (by decide) with h437 | h437
                · rcases m.htr 0 2 4 (by decide) (by decide) with h438 | h438
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h439 | h439
                    · linarith only [h398, h439, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h437, h439, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h437, h438, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h443 | h443
                  · linarith only [h437, h443, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h445 | h445
                    · linarith only [h437, h445, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h398, h435, h445, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
              · linarith only [h400, h435, h436, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h449 | h449
              · rcases m.htr 0 2 3 (by decide) (by decide) with h450 | h450
                · rcases m.htr 0 2 4 (by decide) (by decide) with h451 | h451
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h452 | h452
                    · linarith only [h398, h452, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h450, h452, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h450, h451, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h456 | h456
                  · linarith only [h450, h456, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h458 | h458
                    · linarith only [h450, h458, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h398, h458, hc25, hlam, hphi, p0_1, u2ehi0]
              · linarith only [h400, h449, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h432, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h463 | h463
    · linarith only [h463, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
    · rcases p0_3 (m.d 1 5) (by simp) with h465 | h465
      · rcases p0_3 (m.d 2 5) (by simp) with h466 | h466
        · rcases p0_3 (m.d 3 5) (by simp) with h467 | h467
          · rcases p0_3 (m.d 4 5) (by simp) with h468 | h468
            · linarith only [h468, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h470 | h470
              · linarith only [h465, h470, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi4]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h472 | h472
                · rcases m.htr 0 2 4 (by decide) (by decide) with h473 | h473
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h474 | h474
                    · linarith only [h474, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi4]
                    · linarith only [h467, h472, h474, hc35, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h472, h473, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h478 | h478
                  · linarith only [h472, h478, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h480 | h480
                    · linarith only [h472, h480, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h463, h467, h480, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h483 | h483
            · linarith only [h483, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h485 | h485
              · linarith only [h463, h465, h485, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h487 | h487
                · rcases m.htr 0 2 4 (by decide) (by decide) with h488 | h488
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h489 | h489
                    · linarith only [h463, h489, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h487, h489, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h487, h488, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h493 | h493
                  · linarith only [h487, h493, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h495 | h495
                    · linarith only [h487, h495, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h463, h495, hc25, hlam, hphi, p0_1, u2ehi0]
        · linarith only [h466, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h499 | h499
        · rcases p0_3 (m.d 3 5) (by simp) with h500 | h500
          · rcases p0_3 (m.d 4 5) (by simp) with h501 | h501
            · linarith only [h501, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h503 | h503
              · rcases m.htr 0 2 3 (by decide) (by decide) with h504 | h504
                · rcases m.htr 0 2 4 (by decide) (by decide) with h505 | h505
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h506 | h506
                    · linarith only [h463, h506, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h504, h506, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h504, h505, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h510 | h510
                  · linarith only [h504, h510, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h512 | h512
                    · linarith only [h504, h512, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h463, h500, h512, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
              · linarith only [h465, h500, h503, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h516 | h516
            · linarith only [h516, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h518 | h518
              · rcases m.htr 0 2 3 (by decide) (by decide) with h519 | h519
                · rcases m.htr 0 2 4 (by decide) (by decide) with h520 | h520
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h521 | h521
                    · linarith only [h463, h521, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h519, h521, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h519, h520, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h525 | h525
                  · linarith only [h519, h525, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h527 | h527
                    · linarith only [h519, h527, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h463, h527, hc25, hlam, hphi, p0_1, u2ehi0]
              · linarith only [h465, h518, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h499, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h532 | h532
    · linarith only [h532, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h534 | h534
      · rcases p0_3 (m.d 2 5) (by simp) with h535 | h535
        · rcases p0_3 (m.d 3 5) (by simp) with h536 | h536
          · rcases p0_3 (m.d 4 5) (by simp) with h537 | h537
            · rcases m.htr 0 1 5 (by decide) (by decide) with h538 | h538
              · linarith only [h534, h538, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h540 | h540
                · rcases m.htr 0 2 4 (by decide) (by decide) with h541 | h541
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h542 | h542
                    · linarith only [h535, h542, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h540, h542, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h540, h541, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h546 | h546
                  · linarith only [h540, h546, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h548 | h548
                    · linarith only [h540, h548, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h548, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h551 | h551
              · linarith only [h534, h551, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h553 | h553
                · rcases m.htr 0 2 4 (by decide) (by decide) with h554 | h554
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h555 | h555
                    · linarith only [h535, h555, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h553, h555, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h553, h554, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h559 | h559
                  · linarith only [h553, h559, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h561 | h561
                    · linarith only [h553, h561, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h561, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
          · linarith only [h536, hlam, p0_0]
        · linarith only [h535, hc35, hlam, hphi, ht23, p0_1, u2ehi4]
      · rcases p0_3 (m.d 2 5) (by simp) with h566 | h566
        · rcases p0_3 (m.d 3 5) (by simp) with h567 | h567
          · rcases p0_3 (m.d 4 5) (by simp) with h568 | h568
            · rcases m.htr 0 1 5 (by decide) (by decide) with h569 | h569
              · rcases m.htr 0 2 3 (by decide) (by decide) with h570 | h570
                · rcases m.htr 0 2 4 (by decide) (by decide) with h571 | h571
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h572 | h572
                    · linarith only [h566, h572, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h570, h572, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h570, h571, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h576 | h576
                  · linarith only [h570, h576, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h578 | h578
                    · linarith only [h570, h578, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h578, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
              · linarith only [h534, h569, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h582 | h582
              · rcases m.htr 0 2 3 (by decide) (by decide) with h583 | h583
                · rcases m.htr 0 2 4 (by decide) (by decide) with h584 | h584
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h585 | h585
                    · linarith only [h566, h585, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h583, h585, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h583, h584, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h589 | h589
                  · linarith only [h583, h589, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h591 | h591
                    · linarith only [h583, h591, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h591, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
              · linarith only [h534, h582, hlam]
          · linarith only [h567, hlam, p0_0]
        · linarith only [h566, hc35, hlam, hphi, ht23, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h597 | h597
    · linarith only [h597, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · rcases p0_3 (m.d 1 5) (by simp) with h599 | h599
      · linarith only [h599, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h601 | h601
        · rcases p0_3 (m.d 3 5) (by simp) with h602 | h602
          · rcases p0_3 (m.d 4 5) (by simp) with h603 | h603
            · rcases m.htr 0 1 5 (by decide) (by decide) with h604 | h604
              · linarith only [h597, h604, hlam]
              · linarith only [h601, h604, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h607 | h607
              · linarith only [h597, h607, hlam]
              · linarith only [h607, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h602, hlam, p0_0]
        · linarith only [h601, hc35, hlam, hphi, ht23, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht23, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h614 | h614
    · linarith only [h614, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
    · rcases p0_3 (m.d 1 5) (by simp) with h616 | h616
      · rcases p0_3 (m.d 2 5) (by simp) with h617 | h617
        · rcases p0_3 (m.d 3 5) (by simp) with h618 | h618
          · rcases p0_3 (m.d 4 5) (by simp) with h619 | h619
            · linarith only [h619, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h621 | h621
              · linarith only [h616, h621, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi4]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h623 | h623
                · rcases m.htr 0 2 4 (by decide) (by decide) with h624 | h624
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h625 | h625
                    · linarith only [h617, h625, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi4]
                    · linarith only [h623, h625, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h623, h624, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h629 | h629
                  · linarith only [h623, h629, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h631 | h631
                    · linarith only [h623, h631, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h614, h631, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
          · linarith only [h618, hlam, p0_0]
        · linarith only [h617, hc35, hlam, hphi, ht23, p0_1, u2ehi4]
      · rcases p0_3 (m.d 2 5) (by simp) with h636 | h636
        · rcases p0_3 (m.d 3 5) (by simp) with h637 | h637
          · rcases p0_3 (m.d 4 5) (by simp) with h638 | h638
            · linarith only [h638, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h640 | h640
              · rcases m.htr 0 2 3 (by decide) (by decide) with h641 | h641
                · rcases m.htr 0 2 4 (by decide) (by decide) with h642 | h642
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h643 | h643
                    · linarith only [h614, h636, h643, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h641, h643, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h641, h642, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h647 | h647
                  · linarith only [h641, h647, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h649 | h649
                    · linarith only [h641, h649, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h614, h649, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
              · linarith only [h616, h640, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h637, hlam, p0_0]
        · linarith only [h636, hc35, hlam, hphi, ht23, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h655 | h655
    · linarith only [h655, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h657 | h657
      · rcases p0_3 (m.d 2 5) (by simp) with h658 | h658
        · rcases p0_3 (m.d 3 5) (by simp) with h659 | h659
          · rcases p0_3 (m.d 4 5) (by simp) with h660 | h660
            · rcases m.htr 0 1 5 (by decide) (by decide) with h661 | h661
              · linarith only [h657, h661, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h663 | h663
                · rcases m.htr 0 2 4 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h665 | h665
                    · linarith only [h658, h665, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h663, h665, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h663, h664, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h669 | h669
                  · linarith only [h663, h669, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h671 | h671
                    · linarith only [h663, h671, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h671, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
            · linarith only [h660, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h675 | h675
            · rcases m.htr 0 1 5 (by decide) (by decide) with h676 | h676
              · linarith only [h657, h676, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h678 | h678
                · rcases m.htr 0 2 4 (by decide) (by decide) with h679 | h679
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h680 | h680
                    · linarith only [h658, h680, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h678, h680, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h678, h679, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h684 | h684
                  · linarith only [h678, h684, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h686 | h686
                    · linarith only [h678, h686, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h686, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
            · linarith only [h675, hlam, p0_0]
        · linarith only [h658, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
      · rcases p0_3 (m.d 2 5) (by simp) with h691 | h691
        · rcases p0_3 (m.d 3 5) (by simp) with h692 | h692
          · rcases p0_3 (m.d 4 5) (by simp) with h693 | h693
            · rcases m.htr 0 1 5 (by decide) (by decide) with h694 | h694
              · rcases m.htr 0 2 3 (by decide) (by decide) with h695 | h695
                · rcases m.htr 0 2 4 (by decide) (by decide) with h696 | h696
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h697 | h697
                    · linarith only [h691, h697, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h695, h697, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h695, h696, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h701 | h701
                  · linarith only [h695, h701, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h703 | h703
                    · linarith only [h695, h703, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h692, h703, hc35, hlam, hphi, ht23, p0_1, u2ehi0]
              · linarith only [h657, h694, hlam]
            · linarith only [h693, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h708 | h708
            · rcases m.htr 0 1 5 (by decide) (by decide) with h709 | h709
              · rcases m.htr 0 2 3 (by decide) (by decide) with h710 | h710
                · rcases m.htr 0 2 4 (by decide) (by decide) with h711 | h711
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h712 | h712
                    · linarith only [h691, h712, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h710, h712, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h710, h711, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h716 | h716
                  · linarith only [h710, h716, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h718 | h718
                    · linarith only [h710, h718, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h718, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
              · linarith only [h657, h709, hlam]
            · linarith only [h708, hlam, p0_0]
        · linarith only [h691, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h724 | h724
    · linarith only [h724, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · rcases p0_3 (m.d 1 5) (by simp) with h726 | h726
      · linarith only [h726, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h728 | h728
        · rcases p0_3 (m.d 3 5) (by simp) with h729 | h729
          · rcases p0_3 (m.d 4 5) (by simp) with h730 | h730
            · rcases m.htr 0 1 5 (by decide) (by decide) with h731 | h731
              · linarith only [h724, h731, hlam]
              · linarith only [h728, h731, hc01, hc25, hlam, hphi, ht12, p0_1]
            · linarith only [h730, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h735 | h735
            · rcases m.htr 0 1 5 (by decide) (by decide) with h736 | h736
              · linarith only [h724, h736, hlam]
              · linarith only [h736, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h735, hlam, p0_0]
        · linarith only [h728, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h742 | h742
    · linarith only [h742, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · rcases p0_3 (m.d 1 5) (by simp) with h744 | h744
      · rcases p0_3 (m.d 2 5) (by simp) with h745 | h745
        · rcases p0_3 (m.d 3 5) (by simp) with h746 | h746
          · linarith only [h746, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h748 | h748
            · rcases m.htr 0 1 5 (by decide) (by decide) with h749 | h749
              · linarith only [h744, h749, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi3]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h751 | h751
                · rcases m.htr 0 2 4 (by decide) (by decide) with h752 | h752
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h753 | h753
                    · linarith only [h745, h753, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                    · linarith only [h751, h753, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h751, h752, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h757 | h757
                  · linarith only [h751, h757, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h759 | h759
                    · linarith only [h751, h759, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h742, h759, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
            · linarith only [h748, hlam, p0_0]
        · linarith only [h745, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
      · rcases p0_3 (m.d 2 5) (by simp) with h764 | h764
        · rcases p0_3 (m.d 3 5) (by simp) with h765 | h765
          · linarith only [h765, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h767 | h767
            · rcases m.htr 0 1 5 (by decide) (by decide) with h768 | h768
              · rcases m.htr 0 2 3 (by decide) (by decide) with h769 | h769
                · rcases m.htr 0 2 4 (by decide) (by decide) with h770 | h770
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h771 | h771
                    · linarith only [h742, h764, h771, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                    · linarith only [h769, h771, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h769, h770, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h775 | h775
                  · linarith only [h769, h775, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h777 | h777
                    · linarith only [h769, h777, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h742, h777, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi0]
              · linarith only [h744, h768, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h767, hlam, p0_0]
        · linarith only [h764, hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h2bigk := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                            · linarith only [h0, h12, h14, h3, h6, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h0, h11, h14, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                          · linarith only [h0, h17, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                            · linarith only [h11, h19, h8, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                              · linarith only [h0, h21, h9, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                                · linarith only [h0, h21, h23, h3, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h17, h23, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h10, h5, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h4, h8, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h28, h3, h8, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                      · linarith only [h0, h3, h30, h8, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                                · linarith only [h0, h3, h33, h36, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h0, h3, h33, h35, h36, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h28, h35, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h28, h33, h34, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h3, h32, h33, h6, h8, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                            · linarith only [h0, h3, h32, h43, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h42, h43, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h0, h3, h42, h6, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h48 | h48
                · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                          · linarith only [h48, h53, h6, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                            · linarith only [h0, h50, h53, h55, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h1, h52, h55, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h48, h52, h6, hc13, hc34, hlam, hphi]
                      · linarith only [h50, h51, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h0, h4, h49, h50, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h61 | h61
                    · linarith only [h0, h3, h49, h61, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                      · linarith only [h0, h3, h49, h63, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                          · linarith only [h0, h3, h6, h66, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                                · rcases h2bigk with h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    rcases p71_3 (m.d 0 2) (by simp) with h73 | h73
                                    · rcases p71_3 (m.d 1 2) (by simp) with h74 | h74
                                      · linarith only [h0, h74, hlam]
                                      · rcases p71_3 (m.d 2 3) (by simp) with h76 | h76
                                        · linarith only [h3, h76, hlam]
                                        · linarith only [h49, h76, hlam]
                                    · linarith only [h0, h73, hlam]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h0, h63, h68, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u0elo0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h0, h61, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u0elo0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h0, h63, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u0elo0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h0, hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h49, hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h61, hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h63, hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h3, hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u0elo0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h66, hlam, p71_1]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h63, hc12, hc23, hlam, hphi, p71_1]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h4, hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h0, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u0elo0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h0, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p71_1, u0elo0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h0, h4, h63, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u0elo0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h5, hlam, p71_0]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p71_1, u5elo2]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h68, hlam, p71_1]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [h69, hlam, p71_1]
                                  · have p71_0 := h71c.1
                                    have p71_1 := h71c.2.1
                                    have p71_2 := h71c.2.2.1
                                    have p71_3 := h71c.2.2.2
                                    linarith only [hlam, p71_0]
                                · linarith only [h48, h6, h70, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                              · linarith only [h63, h66, h68, h69, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h1, h65, h68, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h48, h6, h65, hc13, hc34, hlam, hphi]
                · linarith only [h48, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
            · linarith only [h3, h5, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h109 | h109
            · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
              · linarith only [h110, h3, h4, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
                · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                    · linarith only [h112, h114, h3, h4, hc12, hlam, hphi, ht01, u0ehi9]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h117 | h117
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                          · linarith only [h110, h112, h118, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                            · linarith only [h0, h113, h120, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h1, h112, h117, h118, h120, h3, h4, hc23, hc34, hlam, hphi, u0ehi9, u0elo0]
                        · linarith only [h110, h112, h117, hc13, hc34, hlam, hphi]
                      · linarith only [h109, h116, h4, hc12, hc24, hlam, hphi]
                  · linarith only [h113, h3, h4, hc12, hc24, hlam, hphi]
                · linarith only [h112, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
            · linarith only [h109, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h128 | h128
          · rcases m.htr 0 2 5 (by decide) (by decide) with h129 | h129
            · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
              · rcases m.htr 0 3 5 (by decide) (by decide) with h131 | h131
                · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
                  · linarith only [h128, h132, h3, hc12, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
                              · linarith only [h0, h134, h139, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                                · linarith only [h130, h139, h141, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · rcases h2bigk with h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h3, hc12, hc23, hlam, hphi, p143_1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h3, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    rcases p143_3 (m.d 0 2) (by simp) with h147 | h147
                                    · rcases p143_3 (m.d 1 2) (by simp) with h148 | h148
                                      · linarith only [h0, h148, hlam]
                                      · linarith only [h134, h148, hlam]
                                    · linarith only [h147, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    rcases p143_3 (m.d 0 2) (by simp) with h152 | h152
                                    · rcases p143_3 (m.d 1 2) (by simp) with h153 | h153
                                      · linarith only [h0, h153, hlam]
                                      · linarith only [h135, h153, hlam]
                                    · linarith only [h152, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h0, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h132, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h0, h137, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1, u0elo0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h1, h132, h137, h139, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1, u0elo0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p143_1, u0ehi6]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    rcases p143_3 (m.d 0 2) (by simp) with h163 | h163
                                    · linarith only [h163, h3, hlam]
                                    · linarith only [h0, h163, hlam]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    rcases p143_3 (m.d 0 2) (by simp) with h167 | h167
                                    · linarith only [h167, h3, hlam]
                                    · linarith only [h128, h167, hlam]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    rcases p143_3 (m.d 0 2) (by simp) with h170 | h170
                                    · linarith only [h170, h3, hlam]
                                    · linarith only [h129, h170, hlam]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h128, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h134, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h137, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h139, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h129, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h135, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h138, hlam, p143_1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h135, h137, hc34, hlam, hphi, ht45, p143_1, u5elo1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [hlam, p143_0]
                            · linarith only [h128, h138, h3, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo3]
                          · linarith only [h128, h137, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                        · linarith only [h132, h134, h136, hc24, hlam, hphi, ht45, u5elo3]
                      · linarith only [h134, h135, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h128, h134, h3, hc12, hc23, hlam, hphi]
                · linarith only [h130, h131, hc34, hlam, hphi, ht45, u5elo3]
              · linarith only [h128, h130, h3, hlam]
            · linarith only [h128, h129, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h191 | h191
            · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
              · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
                · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
                  · linarith only [h191, h194, h3, hc12, hlam, hphi, ht01, u0ehi9]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                    · linarith only [h1, h128, h191, h194, h196, hlam, hphi, u0ehi9, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h198 | h198
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                                · rcases h2bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h128, h200, hc12, hc23, hlam, hphi, p204_1]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h3, hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h128, hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    rcases p204_3 (m.d 0 2) (by simp) with h209 | h209
                                    · rcases p204_3 (m.d 1 2) (by simp) with h210 | h210
                                      · linarith only [h0, h210, hlam]
                                      · linarith only [h198, h210, hlam]
                                    · linarith only [h209, hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h0, hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h194, hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h196, hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h0, h201, h203, hc45, hlam, hphi, ht0b, ht5b, p204_1, u0elo0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p204_1, u0ehi6]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    rcases p204_3 (m.d 0 2) (by simp) with h220 | h220
                                    · linarith only [h220, h3, hlam]
                                    · linarith only [h0, h220, hlam]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h128, h191, hc23, hlam, hphi, ht01, ht12, p204_1, u0ehi9]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    rcases p204_3 (m.d 0 2) (by simp) with h225 | h225
                                    · linarith only [h225, h3, hlam]
                                    · linarith only [h191, h225, hlam]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h191, hc24, hlam, hphi, ht01, ht12, p204_1, u0ehi9]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    rcases p204_3 (m.d 0 2) (by simp) with h229 | h229
                                    · linarith only [h128, h229, hlam]
                                    · linarith only [h0, h229, hlam]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h200, hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    rcases p204_3 (m.d 0 2) (by simp) with h234 | h234
                                    · linarith only [h128, h234, hlam]
                                    · linarith only [h191, h234, hlam]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h191, hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h198, hlam, p204_0]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h201, hlam, p204_1]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [h202, hlam, p204_1]
                                  · have p204_0 := h204c.1
                                    have p204_1 := h204c.2.1
                                    have p204_2 := h204c.2.2.1
                                    have p204_3 := h204c.2.2.2
                                    linarith only [hlam, p204_0]
                                · linarith only [h0, h198, h202, h203, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h128, h191, h202, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo4]
                            · linarith only [h1, h199, h201, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h191, h200, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                        · linarith only [h194, h198, h199, hc25, hlam, hphi, u5elo3]
                      · linarith only [h191, h198, h3, hc12, hc23, hlam, hphi]
                · linarith only [h128, h191, h192, h193, hc25, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h249 | h249
                · rcases m.htr 1 2 3 (by decide) (by decide) with h250 | h250
                  · linarith only [h191, h250, h3, hc12, hlam, hphi, ht01, u0ehi9]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h252 | h252
                    · linarith only [h128, h191, h252, hc12, hlam, hphi, ht01, u0ehi9]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h255 | h255
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                          · linarith only [h192, h256, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                          · linarith only [h191, h256, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                        · linarith only [h192, h249, h250, h255, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h191, h254, h3, hc12, hc23, hlam, hphi]
                · linarith only [h191, h249, h3, hc25, hlam, hphi, u5elo3]
            · linarith only [h191, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo2]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h264 | h264
      · rcases m.htr 0 2 3 (by decide) (by decide) with h265 | h265
        · linarith only [h0, h1, h265, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h267 | h267
          · rcases m.htr 0 2 5 (by decide) (by decide) with h268 | h268
            · rcases m.htr 0 3 4 (by decide) (by decide) with h269 | h269
              · rcases m.htr 0 3 5 (by decide) (by decide) with h270 | h270
                · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
                  · linarith only [h265, h267, h271, hc12, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h275 | h275
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h278 | h278
                              · linarith only [h0, h273, h278, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h280 | h280
                                · linarith only [h276, h278, h280, hlam]
                                · rcases h2bigk with h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h0, h1, h271, h274, h276, h278, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p282_1]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h265, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    rcases p282_3 (m.d 0 2) (by simp) with h286 | h286
                                    · rcases p282_3 (m.d 1 2) (by simp) with h287 | h287
                                      · linarith only [h0, h287, hlam]
                                      · linarith only [h273, h287, hlam]
                                    · linarith only [h286, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    rcases p282_3 (m.d 0 2) (by simp) with h291 | h291
                                    · rcases p282_3 (m.d 1 2) (by simp) with h292 | h292
                                      · linarith only [h0, h292, hlam]
                                      · linarith only [h274, h292, hlam]
                                    · linarith only [h291, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h0, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h271, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h0, h1, h271, h276, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p282_1]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h0, h1, h271, h276, h278, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p282_1]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p282_1, u0ehi6]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    rcases p282_3 (m.d 0 2) (by simp) with h302 | h302
                                    · linarith only [h265, h302, hlam]
                                    · linarith only [h0, h302, hlam]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h0, h1, h271, h273, hlam, p282_2]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h0, h1, h271, h274, hlam, p282_2]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h267, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h273, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h276, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h278, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h268, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h274, hlam, p282_0]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h277, hlam, p282_1]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [h0, h1, h271, h274, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p282_1]
                                  · have p282_0 := h282c.1
                                    have p282_1 := h282c.2.1
                                    have p282_2 := h282c.2.2.1
                                    have p282_3 := h282c.2.2.2
                                    linarith only [hlam, p282_0]
                            · linarith only [h0, h1, h271, h277, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h271, h276, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1, h267, h275, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                      · linarith only [h273, h274, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h0, h1, h267, h271, h273, hc12, hc23, hlam, hphi]
                · linarith only [h269, h270, hc34, hlam, hphi, ht45, u5elo3]
              · linarith only [h0, h1, h267, h269, hlam]
            · linarith only [h267, h268, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h326 | h326
            · rcases m.htr 0 3 4 (by decide) (by decide) with h327 | h327
              · rcases m.htr 0 3 5 (by decide) (by decide) with h328 | h328
                · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
                  · linarith only [h265, h326, h329, hc12, hlam, hphi, ht01, u0ehi9]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                    · linarith only [h0, h267, h326, h331, hlam, hphi, u0ehi9, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h333 | h333
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h334 | h334
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h338 | h338
                                · rcases h2bigk with h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h267, hc12, hc24, hlam, hphi, p339_1]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h265, hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h267, hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    rcases p339_3 (m.d 0 2) (by simp) with h344 | h344
                                    · rcases p339_3 (m.d 1 2) (by simp) with h345 | h345
                                      · linarith only [h0, h345, hlam]
                                      · linarith only [h333, h345, hlam]
                                    · linarith only [h344, hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h0, hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h329, hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h331, hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h0, h336, h338, hc45, hlam, hphi, ht0b, ht5b, p339_1, u0elo0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p339_1, u0ehi6]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    rcases p339_3 (m.d 0 2) (by simp) with h355 | h355
                                    · linarith only [h265, h355, hlam]
                                    · linarith only [h0, h355, hlam]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h267, h326, hc23, hlam, hphi, ht01, ht12, p339_1, u0ehi9]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h0, h1, h329, h333, hlam, p339_2]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h326, hc24, hlam, hphi, ht01, ht12, p339_1, u0ehi9]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    rcases p339_3 (m.d 0 2) (by simp) with h362 | h362
                                    · linarith only [h267, h362, hlam]
                                    · linarith only [h0, h362, hlam]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h335, hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    rcases p339_3 (m.d 0 2) (by simp) with h367 | h367
                                    · linarith only [h267, h367, hlam]
                                    · linarith only [h326, h367, hlam]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h326, hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h333, hlam, p339_0]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h336, hlam, p339_1]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [h337, hlam, p339_1]
                                  · have p339_0 := h339c.1
                                    have p339_1 := h339c.2.1
                                    have p339_2 := h339c.2.2.1
                                    have p339_3 := h339c.2.2.2
                                    linarith only [hlam, p339_0]
                                · linarith only [h0, h1, h329, h333, h337, h338, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h267, h326, h337, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo4]
                            · linarith only [h0, h1, h329, h336, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h326, h327, h329, h335, hlam, hphi, u0ehi9, u0elo2]
                        · linarith only [h0, h1, h326, h334, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                      · linarith only [h0, h1, h326, h329, h333, hc12, hc23, hlam, hphi]
                · linarith only [h327, h328, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h382 | h382
                · rcases m.htr 1 2 3 (by decide) (by decide) with h383 | h383
                  · linarith only [h0, h1, h327, h383, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h385 | h385
                    · linarith only [h0, h1, h267, h327, h385, hc02, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h388 | h388
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h389 | h389
                          · linarith only [h0, h1, h327, h389, hc12, hc23, hlam, hphi]
                          · linarith only [h265, h326, h389, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                        · linarith only [h0, h1, h326, h388, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                      · linarith only [h0, h1, h326, h383, h387, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h326, h382, hc25, hlam, hphi, u5elo3]
            · linarith only [h326, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo2]
      · linarith only [h0, h264, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h397 | h397
    · rcases m.htr 0 1 5 (by decide) (by decide) with h398 | h398
      · rcases m.htr 0 2 3 (by decide) (by decide) with h399 | h399
        · rcases m.htr 0 2 4 (by decide) (by decide) with h400 | h400
          · rcases m.htr 0 2 5 (by decide) (by decide) with h401 | h401
            · rcases m.htr 0 3 4 (by decide) (by decide) with h402 | h402
              · rcases m.htr 0 3 5 (by decide) (by decide) with h403 | h403
                · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h406 | h406
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h409 | h409
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h410 | h410
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h411 | h411
                                · linarith only [h397, h404, h408, h411, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h0, h397, h404, h408, h410, h411, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
                                · linarith only [h0, h397, h402, h410, h414, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases h2bigk with h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h0, hlam, p416_1]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h409, hc35, hlam, hphi, ht0b, ht5b, p416_1, u0elo1]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    rcases p416_3 (m.d 0 2) (by simp) with h420 | h420
                                    · rcases p416_3 (m.d 1 2) (by simp) with h421 | h421
                                      · rcases p416_3 (m.d 2 3) (by simp) with h422 | h422
                                        · linarith only [h399, h422, hlam]
                                        · linarith only [h408, h422, hlam]
                                      · linarith only [h405, h421, hlam]
                                    · linarith only [h420, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    rcases p416_3 (m.d 0 2) (by simp) with h427 | h427
                                    · rcases p416_3 (m.d 1 2) (by simp) with h428 | h428
                                      · rcases p416_3 (m.d 2 3) (by simp) with h429 | h429
                                        · linarith only [h399, h429, hlam]
                                        · linarith only [h409, h429, hlam]
                                      · linarith only [h406, h428, hlam]
                                    · linarith only [h427, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, p416_1, u0ehi5]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    rcases p416_3 (m.d 0 2) (by simp) with h436 | h436
                                    · linarith only [h0, h436, hlam]
                                    · linarith only [h399, h436, hlam]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    rcases p416_3 (m.d 0 2) (by simp) with h439 | h439
                                    · linarith only [h0, h439, hlam]
                                    · linarith only [h400, h439, hlam]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    rcases p416_3 (m.d 0 2) (by simp) with h442 | h442
                                    · linarith only [h0, h442, hlam]
                                    · linarith only [h401, h442, hlam]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h399, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h404, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h397, h404, hc24, hlam, hphi, ht0b, ht45, ht5b, p416_1, u0elo0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h0, h397, h404, h408, h410, hc34, hlam, hphi, ht0b, ht45, ht5b, p416_1, u0elo1]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h400, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h405, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h408, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h410, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h401, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h406, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h409, hlam, p416_1]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h408, hc34, hlam, hphi, ht45, p416_1, u5elo2]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [hlam, p416_0]
                            · linarith only [h0, h397, h407, h409, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h461 | h461
                            · linarith only [h0, h397, h402, h408, h461, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h0, h397, h407, h461, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                          · linarith only [h0, h397, h403, h404, h407, h464, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h466 | h466
                            · linarith only [h404, h407, h466, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h468 | h468
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h469 | h469
                                · rcases h2bigk with h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h0, hlam, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    rcases p470_3 (m.d 0 2) (by simp) with h473 | h473
                                    · rcases p470_3 (m.d 1 2) (by simp) with h474 | h474
                                      · rcases p470_3 (m.d 2 3) (by simp) with h475 | h475
                                        · linarith only [h475, hlam, p470_0]
                                        · rcases p470_3 (m.d 2 4) (by simp) with h477 | h477
                                          · linarith only [h400, h477, hlam]
                                          · linarith only [h464, h477, hlam]
                                      · linarith only [h404, h474, hlam]
                                    · linarith only [h473, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h468, hc45, hlam, hphi, ht0b, ht5b, p470_1, u0elo1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    rcases p470_3 (m.d 0 2) (by simp) with h483 | h483
                                    · rcases p470_3 (m.d 1 2) (by simp) with h484 | h484
                                      · rcases p470_3 (m.d 2 3) (by simp) with h485 | h485
                                        · linarith only [h399, h485, hlam]
                                        · rcases p470_3 (m.d 2 4) (by simp) with h487 | h487
                                          · linarith only [h400, h487, hlam]
                                          · linarith only [h468, h487, hlam]
                                      · linarith only [h406, h484, hlam]
                                    · linarith only [h483, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h0, h397, h402, h407, h469, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h0, h397, h402, h404, h407, h469, hlam, p470_2]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    rcases p470_3 (m.d 0 2) (by simp) with h495 | h495
                                    · linarith only [h0, h495, hlam]
                                    · linarith only [h400, h495, hlam]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    rcases p470_3 (m.d 0 2) (by simp) with h498 | h498
                                    · linarith only [h0, h498, hlam]
                                    · linarith only [h401, h498, hlam]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h399, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h404, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h464, hlam, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h466, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h400, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h405, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h400, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p470_1, u0elo1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h397, h402, h464, hc25, hlam, hphi, ht0b, ht5b, p470_1, u0elo0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h401, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h406, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht34, ht45, p470_1, u5elo2]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h468, hlam, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hlam, p470_0]
                                · linarith only [h464, h469, hc23, hlam, hphi, ht34, ht45, u5elo4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h517 | h517
                                · linarith only [h0, h397, h402, h468, h517, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h464, h517, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h406, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h397, h402, h405, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                  · linarith only [h0, h397, h402, h404, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                · linarith only [h402, h403, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h524 | h524
                · rcases m.htr 1 2 3 (by decide) (by decide) with h525 | h525
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h526 | h526
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h527 | h527
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h528 | h528
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h529 | h529
                          · linarith only [h397, h402, h525, h529, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h531 | h531
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h532 | h532
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h533 | h533
                                · rcases h2bigk with h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h0, hlam, p534_1]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h531, h533, hc45, hlam, hphi, ht0b, ht5b, p534_1, u0elo1]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h529, h531, h533, hc45, hlam, hphi, ht0b, ht5b, p534_1, u0elo1]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    rcases p534_3 (m.d 0 2) (by simp) with h539 | h539
                                    · rcases p534_3 (m.d 1 2) (by simp) with h540 | h540
                                      · rcases p534_3 (m.d 2 3) (by simp) with h541 | h541
                                        · linarith only [h399, h541, hlam]
                                        · linarith only [h531, h541, hlam]
                                      · linarith only [h527, h540, hlam]
                                    · linarith only [h539, hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p534_1, u0ehi6]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    rcases p534_3 (m.d 0 2) (by simp) with h548 | h548
                                    · linarith only [h0, h548, hlam]
                                    · linarith only [h399, h548, hlam]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    rcases p534_3 (m.d 0 2) (by simp) with h551 | h551
                                    · linarith only [h0, h551, hlam]
                                    · linarith only [h400, h551, hlam]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    rcases p534_3 (m.d 0 2) (by simp) with h554 | h554
                                    · linarith only [h0, h554, hlam]
                                    · linarith only [h401, h554, hlam]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h399, hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h525, hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h529, hlam, p534_1]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h399, hc25, hlam, hphi, ht0b, ht5b, p534_1, u0elo1]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h400, hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h526, hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h400, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p534_1, u0elo1]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h400, h531, h533, hc45, hlam, hphi, ht0b, ht5b, p534_1, u0elo1]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h401, hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h527, hlam, p534_0]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h531, hlam, p534_1]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [h532, hlam, p534_1]
                                  · have p534_0 := h534c.1
                                    have p534_1 := h534c.2.1
                                    have p534_2 := h534c.2.2.1
                                    have p534_3 := h534c.2.2.2
                                    linarith only [hlam, p534_0]
                                · linarith only [h402, h524, h533, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                              · linarith only [h529, h531, h532, hc35, hlam, hphi, u5elo4]
                            · linarith only [h402, h524, h531, hc23, hc34, hlam, hphi]
                        · linarith only [h402, h524, h528, hc13, hc34, hlam, hphi]
                      · linarith only [h0, h527, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h526, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h397, h524, h525, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h524, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
            · linarith only [h399, h401, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h581 | h581
            · rcases m.htr 0 3 4 (by decide) (by decide) with h582 | h582
              · linarith only [h0, h397, h400, h582, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h584 | h584
                · rcases m.htr 1 2 3 (by decide) (by decide) with h585 | h585
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h586 | h586
                    · linarith only [h0, h400, h586, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h397, h584, h586, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h0, h397, h584, h585, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h584, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
            · linarith only [h0, h397, h581, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo2]
        · linarith only [h0, h397, h399, hlam]
      · linarith only [h397, h398, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h594 | h594
      · rcases m.htr 0 2 3 (by decide) (by decide) with h595 | h595
        · rcases m.htr 0 2 4 (by decide) (by decide) with h596 | h596
          · rcases m.htr 0 2 5 (by decide) (by decide) with h597 | h597
            · rcases m.htr 0 3 4 (by decide) (by decide) with h598 | h598
              · rcases m.htr 0 3 5 (by decide) (by decide) with h599 | h599
                · rcases m.htr 1 2 3 (by decide) (by decide) with h600 | h600
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h601 | h601
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h602 | h602
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h603 | h603
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h605 | h605
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h606 | h606
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                                · linarith only [h595, h604, h607, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                · linarith only [h595, h604, h606, h607, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h610 | h610
                                · linarith only [h595, h598, h606, h610, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases h2bigk with h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h0, hlam, p612_1]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h605, hc35, hlam, hphi, ht0b, ht5b, p612_1, u0elo1]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    rcases p612_3 (m.d 0 2) (by simp) with h616 | h616
                                    · rcases p612_3 (m.d 1 2) (by simp) with h617 | h617
                                      · rcases p612_3 (m.d 2 3) (by simp) with h618 | h618
                                        · linarith only [h595, h618, hlam]
                                        · linarith only [h604, h618, hlam]
                                      · linarith only [h601, h617, hlam]
                                    · linarith only [h616, hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    rcases p612_3 (m.d 0 2) (by simp) with h623 | h623
                                    · rcases p612_3 (m.d 1 2) (by simp) with h624 | h624
                                      · rcases p612_3 (m.d 2 3) (by simp) with h625 | h625
                                        · linarith only [h595, h625, hlam]
                                        · linarith only [h605, h625, hlam]
                                      · linarith only [h602, h624, hlam]
                                    · linarith only [h623, hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h397, h595, hc12, hlam, hphi, ht01, p612_1, u0ehi5]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    rcases p612_3 (m.d 0 2) (by simp) with h632 | h632
                                    · linarith only [h0, h632, hlam]
                                    · linarith only [h595, h632, hlam]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    rcases p612_3 (m.d 0 2) (by simp) with h635 | h635
                                    · linarith only [h0, h635, hlam]
                                    · linarith only [h596, h635, hlam]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    rcases p612_3 (m.d 0 2) (by simp) with h638 | h638
                                    · linarith only [h0, h638, hlam]
                                    · linarith only [h597, h638, hlam]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h595, hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h600, hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h595, h604, hc34, hlam, hphi, ht0b, ht45, ht5b, p612_1, u0elo1]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h595, h605, h610, hc34, hlam, hphi, ht0b, ht45, ht5b, p612_1, u0elo1]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h596, hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h601, hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h604, hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h606, hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h597, hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h602, hlam, p612_0]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h605, hlam, p612_1]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [h604, hc34, hlam, hphi, ht45, p612_1, u5elo2]
                                  · have p612_0 := h612c.1
                                    have p612_1 := h612c.2.1
                                    have p612_2 := h612c.2.2.1
                                    have p612_3 := h612c.2.2.2
                                    linarith only [hlam, p612_0]
                            · linarith only [h594, h603, h604, h605, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h657 | h657
                            · linarith only [h595, h598, h604, h657, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h659 | h659
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h660 | h660
                                · rcases h2bigk with h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h0, hlam, p661_1]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    rcases p661_3 (m.d 0 2) (by simp) with h664 | h664
                                    · rcases p661_3 (m.d 1 2) (by simp) with h665 | h665
                                      · rcases p661_3 (m.d 2 3) (by simp) with h666 | h666
                                        · linarith only [h666, hlam, p661_0]
                                        · rcases p661_3 (m.d 2 4) (by simp) with h668 | h668
                                          · linarith only [h596, h668, hlam]
                                          · linarith only [h604, h668, hlam]
                                      · linarith only [h600, h665, hlam]
                                    · linarith only [h664, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h659, hc45, hlam, hphi, ht0b, ht5b, p661_1, u0elo1]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    rcases p661_3 (m.d 0 2) (by simp) with h674 | h674
                                    · rcases p661_3 (m.d 1 2) (by simp) with h675 | h675
                                      · rcases p661_3 (m.d 2 3) (by simp) with h676 | h676
                                        · linarith only [h595, h676, hlam]
                                        · rcases p661_3 (m.d 2 4) (by simp) with h678 | h678
                                          · linarith only [h596, h678, hlam]
                                          · linarith only [h659, h678, hlam]
                                      · linarith only [h602, h675, hlam]
                                    · linarith only [h674, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p661_1, u0ehi6]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h397, h594, h600, h603, h657, hlam, p661_2]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    rcases p661_3 (m.d 0 2) (by simp) with h686 | h686
                                    · linarith only [h0, h686, hlam]
                                    · linarith only [h596, h686, hlam]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    rcases p661_3 (m.d 0 2) (by simp) with h689 | h689
                                    · linarith only [h0, h689, hlam]
                                    · linarith only [h597, h689, hlam]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h595, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h600, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h604, hlam, p661_1]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h657, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h596, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h601, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h596, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p661_1, u0elo1]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h598, h604, hc25, hlam, hphi, ht0b, ht5b, p661_1, u0elo2]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h597, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h602, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht34, ht45, p661_1, u5elo2]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h659, hlam, p661_1]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hlam, p661_0]
                                · linarith only [h604, h660, hc23, hlam, hphi, ht34, ht45, u5elo4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h708 | h708
                                · linarith only [h595, h598, h659, h708, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h604, h708, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h397, h603, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h0, h594, h602, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo2]
                    · linarith only [h397, h594, h600, h601, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h0, h594, h600, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h599, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h716 | h716
                · rcases m.htr 1 2 3 (by decide) (by decide) with h717 | h717
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h718 | h718
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h719 | h719
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h720 | h720
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h721 | h721
                          · linarith only [h397, h594, h595, h598, h721, hlam, hphi, u0ehi9, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h723 | h723
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h724 | h724
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h725 | h725
                                · rcases h2bigk with h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h0, hlam, p726_1]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h723, hc35, hlam, hphi, ht0b, ht5b, p726_1, u0elo1]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h721, h723, h725, hc45, hlam, hphi, ht0b, ht5b, p726_1, u0elo1]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    rcases p726_3 (m.d 0 2) (by simp) with h731 | h731
                                    · rcases p726_3 (m.d 1 2) (by simp) with h732 | h732
                                      · rcases p726_3 (m.d 2 3) (by simp) with h733 | h733
                                        · linarith only [h595, h733, hlam]
                                        · linarith only [h723, h733, hlam]
                                      · linarith only [h719, h732, hlam]
                                    · linarith only [h731, hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p726_1, u0ehi6]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    rcases p726_3 (m.d 0 2) (by simp) with h740 | h740
                                    · linarith only [h0, h740, hlam]
                                    · linarith only [h595, h740, hlam]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    rcases p726_3 (m.d 0 2) (by simp) with h743 | h743
                                    · linarith only [h0, h743, hlam]
                                    · linarith only [h596, h743, hlam]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    rcases p726_3 (m.d 0 2) (by simp) with h746 | h746
                                    · linarith only [h0, h746, hlam]
                                    · linarith only [h597, h746, hlam]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h595, hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h717, hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h721, hlam, p726_1]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h595, h723, h725, hc45, hlam, hphi, ht0b, ht5b, p726_1, u0elo1]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h596, hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h718, hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h596, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p726_1, u0elo1]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h596, h723, h725, hc45, hlam, hphi, ht0b, ht5b, p726_1, u0elo1]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h597, hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h719, hlam, p726_0]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h723, hlam, p726_1]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [h724, hlam, p726_1]
                                  · have p726_0 := h726c.1
                                    have p726_1 := h726c.2.1
                                    have p726_2 := h726c.2.2.1
                                    have p726_3 := h726c.2.2.2
                                    linarith only [hlam, p726_0]
                                · linarith only [h397, h594, h598, h725, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                              · linarith only [h721, h723, h724, hc35, hlam, hphi, u5elo4]
                            · linarith only [h598, h716, h723, hc23, hc34, hlam, hphi]
                        · linarith only [h397, h594, h598, h716, h720, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                      · linarith only [h0, h594, h719, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo2]
                    · linarith only [h397, h594, h717, h718, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h0, h594, h717, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h716, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
            · linarith only [h595, h597, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h773 | h773
            · rcases m.htr 0 3 4 (by decide) (by decide) with h774 | h774
              · linarith only [h595, h596, h774, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h776 | h776
                · rcases m.htr 1 2 3 (by decide) (by decide) with h777 | h777
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h778 | h778
                    · linarith only [h397, h594, h595, h596, h778, hc12, hlam, hphi, ht01, u0ehi9]
                    · linarith only [h0, h594, h778, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h0, h594, h777, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h397, h594, h776, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo3]
            · linarith only [h397, h594, h595, h773, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h784 | h784
          · rcases m.htr 0 2 5 (by decide) (by decide) with h785 | h785
            · rcases m.htr 0 3 4 (by decide) (by decide) with h786 | h786
              · rcases m.htr 0 3 5 (by decide) (by decide) with h787 | h787
                · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
                  · linarith only [h595, h788, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h594, h788, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h0, h594, h595, h787, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo3]
              · linarith only [h595, h784, h786, hlam]
            · linarith only [h0, h594, h785, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h794 | h794
            · rcases m.htr 0 3 4 (by decide) (by decide) with h795 | h795
              · rcases m.htr 0 3 5 (by decide) (by decide) with h796 | h796
                · rcases m.htr 1 2 3 (by decide) (by decide) with h797 | h797
                  · linarith only [h0, h594, h595, h797, hc12, hlam, hphi, ht01, u0ehi9]
                  · linarith only [h0, h594, h797, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h0, h594, h784, h795, h796, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h801 | h801
                · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                  · linarith only [h0, h594, h595, h802, hc12, hlam, hphi, ht01, u0ehi9]
                  · linarith only [h0, h594, h802, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h801, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
            · linarith only [h0, h594, h794, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo2]
      · linarith only [h594, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo1]

end R2N4
