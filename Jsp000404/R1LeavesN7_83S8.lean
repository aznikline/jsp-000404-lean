import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_IR_L_I_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
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
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h5, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h10, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h5, h7, hlam, hphi, ht34, ht45, u3ehi1, u5elo2]
              · linarith only [h0, h3, h5, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
              · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                  · linarith only [h0, h15, h17, h2, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h15, h17, h5, hlam]
                · linarith only [h15, h16, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h0, h15, h21, h23, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h22, h23, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h22, h26, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h26, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                      · rcases h2bigk with h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h34 | h34
                          · rcases p32_3 (m.d 1 2) (by simp) with h35 | h35
                            · linarith only [h0, h35, hlam]
                            · rcases p32_3 (m.d 2 3) (by simp) with h37 | h37
                              · linarith only [h2, h37, hlam]
                              · linarith only [h37, h5, hlam]
                          · linarith only [h0, h34, hlam]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h29, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p32_1, u3ehi3]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h42 | h42
                          · rcases p32_3 (m.d 1 2) (by simp) with h43 | h43
                            · linarith only [h0, h43, hlam]
                            · rcases p32_3 (m.d 2 3) (by simp) with h45 | h45
                              · linarith only [h2, h45, hlam]
                              · linarith only [h29, h45, hlam]
                          · linarith only [h42, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h49 | h49
                          · rcases p32_3 (m.d 1 2) (by simp) with h50 | h50
                            · linarith only [h0, h50, hlam]
                            · rcases p32_3 (m.d 2 3) (by simp) with h52 | h52
                              · linarith only [h2, h52, hlam]
                              · linarith only [h30, h52, hlam]
                          · linarith only [h49, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h0, hlam, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h5, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h15, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h21, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h2, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h62 | h62
                          · rcases p32_3 (m.d 1 2) (by simp) with h63 | h63
                            · linarith only [h63, hlam, p32_0]
                            · rcases p32_3 (m.d 2 3) (by simp) with h65 | h65
                              · rcases p32_3 (m.d 2 4) (by simp) with h66 | h66
                                · linarith only [h29, h66, hlam]
                                · linarith only [h15, h66, hlam]
                              · linarith only [h65, hlam, p32_0]
                          · linarith only [h0, h62, hlam]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h0, h2, h31, hc01, hc45, hlam, hphi, ht0b, ht5b, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h0, h2, h21, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h3, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h75 | h75
                          · rcases p32_3 (m.d 1 2) (by simp) with h76 | h76
                            · linarith only [h76, hlam, p32_0]
                            · rcases p32_3 (m.d 2 3) (by simp) with h78 | h78
                              · rcases p32_3 (m.d 2 4) (by simp) with h79 | h79
                                · rcases p32_3 (m.d 2 5) (by simp) with h80 | h80
                                  · linarith only [h31, h80, hlam]
                                  · linarith only [h21, h80, hlam]
                                · linarith only [h79, hlam, p32_0]
                              · linarith only [h5, h78, hlam]
                          · linarith only [h0, h75, hlam]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h29, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h21, hc12, hc24, hlam, hphi, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h4, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p32_1, u5elo2]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h30, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h31, hlam, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                      · linarith only [h15, h31, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h30, h5, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                    · linarith only [h29, h96, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h96, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
          · linarith only [h2, h4, hlam, hphi, ht34, ht45, u3ehi0, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h100 | h100
          · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
            · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
              · linarith only [h0, h102, h3, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                  · linarith only [h0, h101, h105, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h101, h105, h3, hc34, hlam, hphi, u3ehi2]
                · linarith only [h101, h104, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
            · linarith only [h101, h2, h3, hc12, hc24, hlam, hphi]
          · linarith only [h100, h2, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h111 | h111
        · rcases m.htr 0 2 5 (by decide) (by decide) with h112 | h112
          · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
            · linarith only [h111, h113, h2, hc12, hlam, hphi, ht01, u0ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
              · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                      · rcases h2bigk with h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h115, h118, h119, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h2, hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h118, h119, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h118, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h0, hlam, p120_1]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h113, hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h0, h118, h119, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h0, h118, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p120_1, u0ehi1]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h115, h118, h119, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          rcases p120_3 (m.d 0 2) (by simp) with h134 | h134
                          · linarith only [h134, h2, hlam]
                          · linarith only [h111, h134, hlam]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          rcases p120_3 (m.d 0 2) (by simp) with h137 | h137
                          · linarith only [h137, h2, hlam]
                          · linarith only [h112, h137, hlam]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h111, hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h115, hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h117, hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h0, h115, h118, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h112, hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h116, hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h118, hlam, p120_0]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [h119, hlam, p120_1]
                        · have p120_0 := h120c.1
                          have p120_1 := h120c.2.1
                          have p120_2 := h120c.2.2.1
                          have p120_3 := h120c.2.2.2
                          linarith only [hlam, p120_0]
                      · linarith only [h117, h119, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h118, h2, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h111, h117, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                · linarith only [h115, h116, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h111, h115, h2, hc12, hc23, hlam, hphi]
          · linarith only [h111, h112, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h156 | h156
          · rcases m.htr 1 2 3 (by decide) (by decide) with h157 | h157
            · linarith only [h156, h157, h2, hc12, hlam, hphi, ht01, u0ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
              · linarith only [h0, h111, h159, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h163 | h163
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                      · rcases h2bigk with h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h111, h161, h162, h163, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p165_1, u3ehi4]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h2, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h111, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h111, h162, h163, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p165_1, u3ehi4]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h0, hlam, p165_1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h157, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h159, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h0, h163, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1, u3ehi4]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p165_1, u0ehi1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h161, h163, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p165_1, u3ehi4]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h111, h156, h163, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p165_1, u3ehi4]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          rcases p165_3 (m.d 0 2) (by simp) with h180 | h180
                          · linarith only [h180, h2, hlam]
                          · linarith only [h156, h180, hlam]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h0, h161, h163, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p165_1, u3ehi4]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h161, h163, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p165_1, u3ehi4]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h162, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          rcases p165_3 (m.d 0 2) (by simp) with h187 | h187
                          · linarith only [h111, h187, hlam]
                          · linarith only [h156, h187, hlam]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h156, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h161, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h163, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h164, hlam, p165_1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hlam, p165_0]
                      · linarith only [h0, h111, h161, h163, h164, hlam, hphi, ht34, ht45, u3ehi4, u5elo4]
                    · linarith only [h162, h163, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h162, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h156, h161, h2, hc12, hc23, hlam, hphi]
          · linarith only [h156, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h201 | h201
    · rcases m.htr 0 2 3 (by decide) (by decide) with h202 | h202
      · rcases m.htr 0 2 4 (by decide) (by decide) with h203 | h203
        · rcases m.htr 0 2 5 (by decide) (by decide) with h204 | h204
          · rcases m.htr 1 2 3 (by decide) (by decide) with h205 | h205
            · rcases m.htr 1 2 4 (by decide) (by decide) with h206 | h206
              · rcases m.htr 1 2 5 (by decide) (by decide) with h207 | h207
                · rcases m.htr 2 3 4 (by decide) (by decide) with h208 | h208
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h210 | h210
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
                          linarith only [h0, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h208, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p211_1, u3ehi3]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          rcases p211_3 (m.d 0 2) (by simp) with h215 | h215
                          · rcases p211_3 (m.d 1 2) (by simp) with h216 | h216
                            · rcases p211_3 (m.d 2 3) (by simp) with h217 | h217
                              · linarith only [h202, h217, hlam]
                              · linarith only [h208, h217, hlam]
                            · linarith only [h206, h216, hlam]
                          · linarith only [h215, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          rcases p211_3 (m.d 0 2) (by simp) with h222 | h222
                          · rcases p211_3 (m.d 1 2) (by simp) with h223 | h223
                            · rcases p211_3 (m.d 2 3) (by simp) with h224 | h224
                              · linarith only [h202, h224, hlam]
                              · linarith only [h209, h224, hlam]
                            · linarith only [h207, h223, hlam]
                          · linarith only [h222, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p211_1, u0ehi1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h208, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p211_1, u3ehi3]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          rcases p211_3 (m.d 0 2) (by simp) with h232 | h232
                          · linarith only [h0, h232, hlam]
                          · linarith only [h203, h232, hlam]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          rcases p211_3 (m.d 0 2) (by simp) with h235 | h235
                          · linarith only [h0, h235, hlam]
                          · linarith only [h204, h235, hlam]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h202, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h205, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h202, h209, h210, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p211_1, u3ehi4]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h0, h202, h209, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p211_1, u3ehi4]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h203, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h206, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h208, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h0, h203, h209, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p211_1, u3ehi4]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h204, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h207, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h209, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h210, hlam, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hlam, p211_0]
                      · linarith only [h208, h210, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h209, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h255 | h255
                    · linarith only [h208, h255, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h255, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h0, h207, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
              · linarith only [h0, h206, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h201, h205, hc23, hlam, hphi, ht01, ht12, u0ehi4]
          · linarith only [h202, h204, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h262 | h262
          · rcases m.htr 1 2 3 (by decide) (by decide) with h263 | h263
            · rcases m.htr 1 2 4 (by decide) (by decide) with h264 | h264
              · linarith only [h202, h203, h264, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h201, h264, hc24, hlam, hphi, ht01, ht12, u0ehi4]
            · linarith only [h0, h201, h202, h263, hc02, hlam, hphi, u0ehi4]
          · linarith only [h202, h262, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h269 | h269
        · rcases m.htr 0 2 5 (by decide) (by decide) with h270 | h270
          · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
            · linarith only [h0, h201, h202, h271, hc12, hlam, hphi, ht01, u0ehi4]
            · linarith only [h0, h201, h271, hc23, hlam, hphi, ht01, ht12, u0ehi4]
          · linarith only [h0, h201, h270, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h275 | h275
          · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
            · linarith only [h0, h201, h202, h276, hc12, hlam, hphi, ht01, u0ehi4]
            · linarith only [h0, h201, h276, hc23, hlam, hphi, ht01, ht12, u0ehi4]
          · linarith only [h0, h201, h275, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo2]
    · linarith only [h201, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo1]

theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                · linarith only [h0, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                · linarith only [h8, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
            · linarith only [h1, h3, h5, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
              · linarith only [h13, h3, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h13, h3, h4, hc34, hlam, hphi, u3ehi2]
            · linarith only [h12, h3, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
          · linarith only [h0, h17, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
            · linarith only [h0, h19, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
              · linarith only [h0, h21, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                · linarith only [h23, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · linarith only [h0, h1, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h28 | h28
    · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
      · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
        · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
            · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
              · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                · linarith only [h0, h28, h30, h34, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h28, h29, h34, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
              · linarith only [h0, h28, h29, h33, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h28, h32, hc12, hc23, hlam, hphi]
          · linarith only [h0, h30, h31, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
            · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
              · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                  · rcases h2bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [hlam, p45_0]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h40, h43, h44, hlam, hphi, ht0b, ht34, ht45, ht5b, p45_1, u0elo1, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h0, hlam, p45_0]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h43, h44, hlam, hphi, ht0b, ht34, ht45, ht5b, p45_1, u0elo1, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h0, h43, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h28, h43, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [hlam, p45_0]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h30, hlam, p45_0]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h30, h43, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h30, h43, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h28, h43, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h40, h43, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [hlam, p45_0]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      rcases p45_3 (m.d 0 2) (by simp) with h59 | h59
                      · linarith only [h0, h59, hlam]
                      · linarith only [h28, h30, h40, h43, h59, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      rcases p45_3 (m.d 0 2) (by simp) with h62 | h62
                      · linarith only [h0, h62, hlam]
                      · linarith only [h28, h62, hlam]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h28, h30, h40, h43, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h40, hlam, p45_0]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h42, hlam, p45_1]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [hlam, p45_0]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h30, h40, h43, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u3ehi4]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h28, hlam, p45_0]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h41, hlam, p45_0]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h43, hlam, p45_1]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [h44, hlam, p45_0]
                    · have p45_0 := h45c.1
                      have p45_1 := h45c.2.1
                      have p45_2 := h45c.2.2.1
                      have p45_3 := h45c.2.2.2
                      linarith only [hlam, p45_0]
                  · linarith only [h42, h44, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                · linarith only [h30, h43, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h28, h29, h42, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h28, h41, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
            · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
              · rcases m.htr 2 3 5 (by decide) (by decide) with h81 | h81
                · rcases m.htr 2 4 5 (by decide) (by decide) with h82 | h82
                  · rcases h2bigk with h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [hlam, p83_0]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h0, h79, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p83_1, u3ehi4]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h0, hlam, p83_0]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h0, h40, h79, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p83_1, u3ehi4]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h0, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p83_1, u3ehi4]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h40, hc02, hc24, hlam, hphi, p83_1]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [hlam, p83_0]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h30, hlam, p83_0]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h40, hlam, p83_0]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h40, h81, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p83_1, u3ehi4]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h28, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p83_1, u3ehi4]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h79, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p83_1, u3ehi4]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [hlam, p83_0]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h40, h79, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p83_1, u3ehi4]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      rcases p83_3 (m.d 0 2) (by simp) with h98 | h98
                      · linarith only [h0, h98, hlam]
                      · linarith only [h28, h98, hlam]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h28, h81, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p83_1, u3ehi4]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h79, h81, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p83_1, u3ehi4]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h80, hlam, p83_1]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [hlam, p83_0]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      rcases p83_3 (m.d 0 2) (by simp) with h105 | h105
                      · linarith only [h0, h105, h40, h79, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h105, h28, hlam]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h28, hlam, p83_0]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h79, hlam, p83_0]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h81, hlam, p83_1]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [h82, hlam, p83_0]
                    · have p83_0 := h83c.1
                      have p83_1 := h83c.2.1
                      have p83_2 := h83c.2.2.1
                      have p83_3 := h83c.2.2.2
                      linarith only [hlam, p83_0]
                  · linarith only [h40, h79, h81, h82, hc45, hlam, hphi, ht34, u3ehi4]
                · linarith only [h80, h81, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h28, h29, h80, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h28, h79, hc12, hc23, hlam, hphi]
      · linarith only [h29, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h118 | h118
      · rcases m.htr 1 2 3 (by decide) (by decide) with h119 | h119
        · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
          · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
            · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
              · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                · rcases m.htr 2 4 5 (by decide) (by decide) with h124 | h124
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
                      linarith only [h0, h119, hlam, hphi, ht0b, ht34, ht45, ht5b, p125_1, u0elo1, u3ehi0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h0, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h124, h28, hlam, p125_1]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h28, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      rcases p125_3 (m.d 0 2) (by simp) with h131 | h131
                      · linarith only [h131, hlam, p125_0]
                      · rcases p125_3 (m.d 1 2) (by simp) with h133 | h133
                        · rcases p125_3 (m.d 2 3) (by simp) with h134 | h134
                          · linarith only [h119, h134, hlam]
                          · linarith only [h0, h134, hlam]
                        · linarith only [h133, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h0, h118, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p125_1, u3ehi4]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      rcases p125_3 (m.d 0 2) (by simp) with h140 | h140
                      · linarith only [h124, h140, h28, hlam, p125_1]
                      · rcases p125_3 (m.d 1 2) (by simp) with h142 | h142
                        · rcases p125_3 (m.d 2 3) (by simp) with h143 | h143
                          · linarith only [h119, h143, hlam]
                          · linarith only [h122, h143, hlam]
                        · linarith only [h142, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      rcases p125_3 (m.d 0 2) (by simp) with h147 | h147
                      · linarith only [h0, h118, h119, h147, h28, hlam, hphi, ht34, ht45, u3ehi4, u5elo2]
                      · rcases p125_3 (m.d 1 2) (by simp) with h149 | h149
                        · rcases p125_3 (m.d 2 3) (by simp) with h150 | h150
                          · linarith only [h119, h150, hlam]
                          · linarith only [h123, h150, hlam]
                        · linarith only [h149, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      rcases p125_3 (m.d 0 2) (by simp) with h154 | h154
                      · linarith only [h154, hlam, p125_0]
                      · rcases p125_3 (m.d 1 2) (by simp) with h156 | h156
                        · rcases p125_3 (m.d 2 3) (by simp) with h157 | h157
                          · rcases p125_3 (m.d 2 4) (by simp) with h158 | h158
                            · linarith only [h122, h158, hlam]
                            · linarith only [h124, h158, h28, hc45, hlam, hphi, u5elo2]
                          · linarith only [h157, hlam, p125_0]
                        · linarith only [h119, h156, hlam, p125_1]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h119, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h119, h124, h28, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p125_1]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h118, h119, h28, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p125_1, u3ehi4]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      rcases p125_3 (m.d 0 2) (by simp) with h167 | h167
                      · linarith only [h167, hlam, p125_0]
                      · rcases p125_3 (m.d 1 2) (by simp) with h169 | h169
                        · rcases p125_3 (m.d 2 3) (by simp) with h170 | h170
                          · rcases p125_3 (m.d 2 4) (by simp) with h171 | h171
                            · rcases p125_3 (m.d 2 5) (by simp) with h172 | h172
                              · linarith only [h124, h172, hlam]
                              · linarith only [h172, h28, hlam]
                            · linarith only [h171, hlam, p125_0]
                          · linarith only [h0, h170, hlam]
                        · linarith only [h0, h119, h169, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p125_1, u3ehi0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h120, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h122, hlam, p125_1]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h118, h119, h122, h28, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p125_1, u3ehi4]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p125_1, u5elo2]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h121, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h123, hlam, p125_1]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h124, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hlam, p125_0]
                  · linarith only [h122, h124, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                · linarith only [h118, h123, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
              · linarith only [h0, h118, h122, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h118, h119, h121, hlam, hphi, ht34, ht45, u3ehi4, u5elo2]
          · linarith only [h0, h118, h119, h120, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
          · rcases m.htr 1 2 5 (by decide) (by decide) with h193 | h193
            · linarith only [h119, h193, h28, hc02, hc23, hlam, hphi]
            · linarith only [h192, h193, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
            · linarith only [h192, h196, h28, hc02, hc24, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
              · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                  · rcases h2bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h28, hc12, hc25, hlam, hphi, p201_1]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h0, hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h28, hc24, hlam, hphi, ht45, p201_1, u5elo2]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h28, hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h119, hc02, hc23, hlam, hphi, p201_1]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h119, hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h192, hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h196, hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      rcases p201_3 (m.d 0 2) (by simp) with h212 | h212
                      · linarith only [h212, hlam, p201_0]
                      · rcases p201_3 (m.d 1 2) (by simp) with h214 | h214
                        · linarith only [h119, h214, hlam]
                        · rcases p201_3 (m.d 2 3) (by simp) with h216 | h216
                          · rcases p201_3 (m.d 2 4) (by simp) with h217 | h217
                            · linarith only [h198, h217, hlam]
                            · linarith only [h196, h200, h217, hc12, hc23, hlam, hphi, p201_1]
                          · linarith only [h216, hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      rcases p201_3 (m.d 0 2) (by simp) with h221 | h221
                      · linarith only [h0, h221, hlam]
                      · rcases p201_3 (m.d 1 2) (by simp) with h223 | h223
                        · linarith only [h223, hlam, p201_0]
                        · rcases p201_3 (m.d 2 3) (by simp) with h225 | h225
                          · rcases p201_3 (m.d 2 4) (by simp) with h226 | h226
                            · linarith only [h198, h226, hlam]
                            · linarith only [h192, h226, hlam]
                          · linarith only [h225, hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h196, h200, hc12, hc23, hlam, hphi, p201_1]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h196, hc12, hc23, hlam, hphi, p201_1]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      rcases p201_3 (m.d 0 2) (by simp) with h233 | h233
                      · linarith only [h233, hlam, p201_0]
                      · rcases p201_3 (m.d 1 2) (by simp) with h235 | h235
                        · linarith only [h192, h235, hlam]
                        · rcases p201_3 (m.d 2 3) (by simp) with h237 | h237
                          · rcases p201_3 (m.d 2 4) (by simp) with h238 | h238
                            · rcases p201_3 (m.d 2 5) (by simp) with h239 | h239
                              · linarith only [h200, h239, hlam]
                              · linarith only [h239, h28, hlam]
                            · linarith only [h238, hlam, p201_0]
                          · linarith only [h0, h237, hlam]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      rcases p201_3 (m.d 0 2) (by simp) with h244 | h244
                      · linarith only [h198, h244, h28, hlam, hphi, ht34, ht45, u3ehi3, u5elo2]
                      · rcases p201_3 (m.d 1 2) (by simp) with h246 | h246
                        · linarith only [h246, hlam, p201_0]
                        · rcases p201_3 (m.d 2 3) (by simp) with h248 | h248
                          · rcases p201_3 (m.d 2 4) (by simp) with h249 | h249
                            · rcases p201_3 (m.d 2 5) (by simp) with h250 | h250
                              · linarith only [h200, h250, hlam]
                              · linarith only [h196, h250, hlam]
                            · linarith only [h249, hlam, p201_0]
                          · linarith only [h119, h248, hlam]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h198, hlam, p201_1]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h28, hc02, hc24, hlam, hphi, p201_1]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p201_1, u5elo2]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p201_1, u5elo2]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h199, hlam, p201_1]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [h200, hlam, p201_0]
                    · have p201_0 := h201c.1
                      have p201_1 := h201c.2.1
                      have p201_2 := h201c.2.2.1
                      have p201_3 := h201c.2.2.2
                      linarith only [hlam, p201_0]
                  · linarith only [h192, h200, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h118, h119, h199, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · linarith only [h0, h118, h198, hc34, hlam, hphi, u3ehi4]
      · linarith only [h118, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem r1l7_20_12_13_M_LR_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
              · linarith only [h1, h5, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                · linarith only [h0, h1, h5, h9, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h1, h11, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h11, h13, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                        · rcases h2bigk with h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            rcases p17_3 (m.d 0 2) (by simp) with h19 | h19
                            · rcases p17_3 (m.d 1 2) (by simp) with h20 | h20
                              · linarith only [h0, h20, hlam]
                              · rcases p17_3 (m.d 2 3) (by simp) with h22 | h22
                                · linarith only [h1, h22, hlam]
                                · linarith only [h22, h5, hlam]
                            · linarith only [h0, h19, hlam]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p17_1, u0elo0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h15, hc45, hlam, hphi, ht0b, ht5b, p17_1, u0elo0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p17_1, u0elo0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, hlam, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h5, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h7, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h9, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h1, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h13, h16, hc12, hc34, hlam, hphi, ht23, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h11, hlam, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h13, hlam, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h2, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p17_1, u0elo0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h2, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, p17_1, u0elo0, u3ehi1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h13, h2, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, p17_1, u0elo0, u3ehi1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h3, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p17_1, u0elo0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h3, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, p17_1, u0elo0, u3ehi1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h15, hlam, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [hlam, p17_0]
                        · linarith only [h0, h16, h2, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h0, h15, h2, h4, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
            · linarith only [h0, h51, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
              · linarith only [h0, h1, h51, h53, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h1, h51, h55, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                  · linarith only [h0, h1, h57, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h0, h2, h57, h59, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                      · linarith only [h0, h2, h4, h61, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                        · linarith only [h4, h63, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                        · linarith only [h51, h57, h63, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
          · linarith only [h2, h3, h66, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
            · linarith only [h0, h68, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h1, h3, h68, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h71 | h71
        · rcases m.htr 0 4 5 (by decide) (by decide) with h72 | h72
          · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
            · linarith only [h0, h73, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h1, h2, h73, hc12, hc24, hlam, hphi]
          · linarith only [h1, h2, h72, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
          · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
            · linarith only [h0, h78, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h1, h2, h78, hc12, hc24, hlam, hphi]
          · linarith only [h1, h2, h77, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h82 | h82
      · rcases m.htr 0 2 5 (by decide) (by decide) with h83 | h83
        · rcases m.htr 0 4 5 (by decide) (by decide) with h84 | h84
          · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
            · linarith only [h1, h85, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
              · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
                · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                  · linarith only [h0, h87, h89, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                  · linarith only [h1, h82, h84, h89, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                · linarith only [h1, h83, h88, hc12, hc23, hlam, hphi]
              · linarith only [h1, h82, h87, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
            · linarith only [h1, h94, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
              · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                  · linarith only [h0, h96, h98, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                  · linarith only [h1, h83, h84, h98, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                · linarith only [h1, h83, h97, hc12, hc23, hlam, hphi]
              · linarith only [h1, h82, h96, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
          · linarith only [h103, h82, h83, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
            · linarith only [h1, h105, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
              · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                · linarith only [h0, h108, h82, h83, hlam, hphi, u0ehi8, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                  · linarith only [h0, h107, h110, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                  · linarith only [h1, h110, h82, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
              · linarith only [h1, h107, h82, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h114 | h114
        · rcases m.htr 0 4 5 (by decide) (by decide) with h115 | h115
          · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
            · linarith only [h1, h116, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
              · linarith only [h0, h114, h118, h82, hlam, hphi, u0ehi9, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
                · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                    · linarith only [h0, h120, h122, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                    · linarith only [h114, h121, h122, h82, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · linarith only [h1, h114, h121, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                · linarith only [h1, h114, h120, hc12, hc23, hlam, hphi]
          · linarith only [h114, h115, h82, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
          · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
            · linarith only [h1, h129, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h131 | h131
              · linarith only [h0, h131, h82, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                · linarith only [h0, h114, h133, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
                        · rcases h2bigk with h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h114, h135, h137, hc12, hc23, hlam, hphi, p139_1]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h1, hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h82, hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h114, hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h0, hlam, p139_1]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h129, hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h131, hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h133, hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p139_1, u0ehi6]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            rcases p139_3 (m.d 0 2) (by simp) with h151 | h151
                            · linarith only [h1, h151, hlam]
                            · linarith only [h0, h151, hlam]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h82, hc23, hlam, hphi, ht01, ht12, p139_1, u0ehi6]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h114, hc23, hlam, hphi, ht01, ht12, p139_1, u0ehi6]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p139_1, u0ehi6]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            rcases p139_3 (m.d 0 2) (by simp) with h158 | h158
                            · linarith only [h158, h82, hlam]
                            · linarith only [h0, h158, hlam]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h135, hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h114, h135, hc23, hlam, hphi, ht01, ht12, p139_1, u0ehi6]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht12, p139_1, u0ehi6]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            rcases p139_3 (m.d 0 2) (by simp) with h165 | h165
                            · linarith only [h114, h165, hlam]
                            · linarith only [h0, h165, hlam]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h136, hlam, p139_0]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [h137, hlam, p139_1]
                          · have p139_0 := h139c.1
                            have p139_1 := h139c.2.1
                            have p139_2 := h139c.2.2.1
                            have p139_3 := h139c.2.2.2
                            linarith only [hlam, p139_0]
                        · linarith only [h128, h138, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                      · linarith only [h128, h137, h82, hlam, hphi, u0ehi6, u0elo3]
                    · linarith only [h1, h136, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h1, h135, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
            · linarith only [h1, h175, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
              · linarith only [h0, h177, h82, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h179 | h179
                · linarith only [h0, h114, h179, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h183 | h183
                      · linarith only [h128, h181, h183, h82, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h183, h82, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h181, h182, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h181, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h188 | h188
    · rcases m.htr 0 2 4 (by decide) (by decide) with h189 | h189
      · rcases m.htr 0 2 5 (by decide) (by decide) with h190 | h190
        · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
          · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
            · rcases m.htr 1 2 4 (by decide) (by decide) with h193 | h193
              · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
                · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                  · linarith only [h188, h195, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h197 | h197
                    · linarith only [h189, h195, h197, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h200 | h200
                        · rcases h2bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h0, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p201_1, u0elo1, u3ehi2]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h199, hc45, hlam, hphi, ht0b, ht5b, p201_1, u0elo1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h197, hlam, hphi, ht0b, ht34, ht45, ht5b, p201_1, u0elo1, u3ehi2]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p201_1, u0ehi6]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            rcases p201_3 (m.d 0 2) (by simp) with h209 | h209
                            · linarith only [h0, h209, hlam]
                            · linarith only [h188, h209, hlam]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            rcases p201_3 (m.d 0 2) (by simp) with h212 | h212
                            · linarith only [h0, h212, hlam]
                            · linarith only [h189, h212, hlam]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            rcases p201_3 (m.d 0 2) (by simp) with h215 | h215
                            · linarith only [h0, h215, hlam]
                            · linarith only [h190, h215, hlam]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h188, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h192, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h195, hlam, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h197, hlam, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h189, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h193, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h189, hlam, hphi, ht0b, ht34, ht45, ht5b, p201_1, u0elo1, u3ehi2]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h189, h197, hlam, hphi, ht0b, ht34, ht45, ht5b, p201_1, u0elo1, u3ehi2]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h190, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h194, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h190, hlam, hphi, ht0b, ht34, ht45, ht5b, p201_1, u0elo1, u3ehi2]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h199, hlam, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, p201_0]
                        · linarith only [h191, h200, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                      · linarith only [h189, h191, h195, h199, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                · linarith only [h0, h194, hc25, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h193, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h192, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
            · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
              · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
                · rcases m.htr 2 3 4 (by decide) (by decide) with h241 | h241
                  · linarith only [h188, h241, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h243 | h243
                    · linarith only [h189, h241, h243, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h245 | h245
                      · linarith only [h189, h191, h245, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                        · linarith only [h191, h247, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                        · linarith only [h241, h247, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h190, h240, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h239, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h238, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
          · linarith only [h189, h190, h253, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
            · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
              · rcases m.htr 1 2 5 (by decide) (by decide) with h257 | h257
                · linarith only [h188, h190, h257, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h257, hc25, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h189, h256, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h255, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h262 | h262
        · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
          · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
            · rcases m.htr 1 2 4 (by decide) (by decide) with h265 | h265
              · linarith only [h188, h189, h265, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h265, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h188, h264, hlam, hphi, u0ehi5, u0elo1]
          · linarith only [h188, h189, h263, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h270 | h270
          · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
            · rcases m.htr 1 2 4 (by decide) (by decide) with h272 | h272
              · linarith only [h188, h189, h272, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h272, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h188, h271, hlam, hphi, u0ehi5, u0elo1]
          · linarith only [h188, h189, h270, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h277 | h277
      · rcases m.htr 0 2 5 (by decide) (by decide) with h278 | h278
        · rcases m.htr 0 4 5 (by decide) (by decide) with h279 | h279
          · rcases m.htr 1 2 3 (by decide) (by decide) with h280 | h280
            · linarith only [h188, h280, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h280, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
            · linarith only [h188, h283, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h283, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
          · linarith only [h277, h278, h286, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
            · linarith only [h0, h188, h288, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h288, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h291 | h291
        · rcases m.htr 0 4 5 (by decide) (by decide) with h292 | h292
          · rcases m.htr 1 2 3 (by decide) (by decide) with h293 | h293
            · linarith only [h0, h188, h293, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h293, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h277, h291, h292, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h297 | h297
          · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
            · linarith only [h188, h298, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h298, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h301 | h301
            · linarith only [h0, h188, h301, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h301, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
