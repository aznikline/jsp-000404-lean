import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_13_25_L_I_L_R_M_LI (m : N7Model)
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
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
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h5, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h9, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h4, h6, hlam, hphi, ht34, ht45, u3ehi1, u5elo2]
            · linarith only [h0, h2, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h1, h14, h16, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h14, h16, h4, hlam]
              · linarith only [h14, h15, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h1, h14, h20, h21, h22, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h14, h21, h22, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h21, h25, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h25, h4, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
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
                              · linarith only [h1, h37, hlam]
                              · linarith only [h37, h4, hlam]
                          · linarith only [h0, h34, hlam]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h0, h28, h31, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p32_1, u3ehi4]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h42 | h42
                          · rcases p32_3 (m.d 1 2) (by simp) with h43 | h43
                            · linarith only [h0, h43, hlam]
                            · rcases p32_3 (m.d 2 3) (by simp) with h45 | h45
                              · linarith only [h1, h45, hlam]
                              · linarith only [h28, h45, hlam]
                          · linarith only [h42, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h49 | h49
                          · rcases p32_3 (m.d 1 2) (by simp) with h50 | h50
                            · linarith only [h0, h50, hlam]
                            · rcases p32_3 (m.d 2 3) (by simp) with h52 | h52
                              · linarith only [h1, h52, hlam]
                              · linarith only [h29, h52, hlam]
                          · linarith only [h49, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h0, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h4, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h14, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h20, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h1, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h62 | h62
                          · rcases p32_3 (m.d 1 2) (by simp) with h63 | h63
                            · linarith only [h63, hlam, p32_0]
                            · rcases p32_3 (m.d 2 3) (by simp) with h65 | h65
                              · rcases p32_3 (m.d 2 4) (by simp) with h66 | h66
                                · linarith only [h28, h66, hlam]
                                · linarith only [h14, h66, hlam]
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
                          linarith only [h20, h30, hc12, hc23, hlam, hphi, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h0, h1, h20, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h2, hlam, p32_0]
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
                                  · linarith only [h30, h80, hlam]
                                  · linarith only [h20, h80, hlam]
                                · linarith only [h79, hlam, p32_0]
                              · linarith only [h4, h78, hlam]
                          · linarith only [h0, h75, hlam]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h28, hlam, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h20, hc12, hc24, hlam, hphi, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h3, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p32_1, u5elo2]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h29, hlam, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h30, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                      · linarith only [h31, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h14, h30, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h29, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                  · linarith only [h28, h97, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h97, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
        · linarith only [h1, h3, hlam, hphi, ht34, ht45, u3ehi0, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h101 | h101
        · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
          · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
            · linarith only [h0, h103, h2, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
              · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                · linarith only [h0, h102, h106, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h102, h106, h2, hc34, hlam, hphi, u3ehi2]
              · linarith only [h102, h105, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
          · linarith only [h1, h102, h2, hc12, hc24, hlam, hphi]
        · linarith only [h1, h101, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h112 | h112
      · rcases m.htr 0 2 5 (by decide) (by decide) with h113 | h113
        · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
          · linarith only [h0, h1, h112, h114, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h116 | h116
            · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
              · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                      · rcases h2bigk with h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h116, h119, h120, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h1, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h1, h119, h120, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h1, h119, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h0, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h114, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h0, h119, h120, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h0, h1, h119, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h112, h119, h120, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h116, h119, h120, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          rcases p122_3 (m.d 0 2) (by simp) with h136 | h136
                          · linarith only [h1, h136, hlam]
                          · linarith only [h112, h136, hlam]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          rcases p122_3 (m.d 0 2) (by simp) with h139 | h139
                          · linarith only [h1, h139, hlam]
                          · linarith only [h113, h139, hlam]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h112, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h116, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h118, hlam, p122_1]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h0, h116, h119, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h113, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h117, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h119, hlam, p122_1]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h120, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                      · linarith only [h121, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h118, h120, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h1, h119, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h1, h116, h118, hlam]
              · linarith only [h116, h117, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h1, h112, h116, hc12, hc23, hlam, hphi]
        · linarith only [h112, h113, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h159 | h159
        · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
          · linarith only [h0, h1, h159, h160, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
            · linarith only [h0, h112, h162, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h164 | h164
              · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                      · rcases h2bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h112, h164, h165, h166, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h1, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h112, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h112, h165, h166, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h0, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h160, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h162, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h0, h166, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h159, h166, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h164, h166, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h112, h159, h166, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          rcases p169_3 (m.d 0 2) (by simp) with h184 | h184
                          · linarith only [h1, h184, hlam]
                          · linarith only [h159, h184, hlam]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h0, h164, h166, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h164, h166, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h165, hlam, p169_1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          rcases p169_3 (m.d 0 2) (by simp) with h191 | h191
                          · linarith only [h112, h191, hlam]
                          · linarith only [h159, h191, hlam]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h159, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h164, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h166, hlam, p169_1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h167, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                      · linarith only [h168, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h0, h112, h164, h166, h167, hlam, hphi, ht34, ht45, u3ehi4, u5elo4]
                  · linarith only [h1, h166, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                  · linarith only [h165, h202, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1, h202, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h1, h159, h164, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h206 | h206
          · linarith only [h0, h159, h206, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
            · linarith only [h0, h159, h208, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h210 | h210
              · linarith only [h0, h159, h210, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                · rcases m.htr 2 3 5 (by decide) (by decide) with h213 | h213
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h214 | h214
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h215 | h215
                      · rcases h2bigk with h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [hlam, p216_0]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h159, hc12, hlam, hphi, ht23, ht34, ht45, p216_1, u5elo2]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h1, hlam, p216_0]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h112, hlam, p216_0]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h159, hlam, p216_0]
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
                          linarith only [h206, hlam, p216_0]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h208, hlam, p216_0]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h210, hlam, p216_0]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          rcases p216_3 (m.d 0 2) (by simp) with h227 | h227
                          · linarith only [h227, hlam, p216_0]
                          · rcases p216_3 (m.d 1 2) (by simp) with h229 | h229
                            · linarith only [h206, h229, hlam]
                            · rcases p216_3 (m.d 2 3) (by simp) with h231 | h231
                              · rcases p216_3 (m.d 2 4) (by simp) with h232 | h232
                                · linarith only [h212, h232, hlam]
                                · linarith only [h112, h232, hlam]
                              · linarith only [h231, hlam, p216_0]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          rcases p216_3 (m.d 0 2) (by simp) with h236 | h236
                          · linarith only [h1, h236, hlam]
                          · linarith only [h0, h236, hlam]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [hlam, p216_0]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h0, h112, hc12, hc23, hlam, hphi, p216_1]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h0, h159, hc12, hc23, hlam, hphi, p216_1]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          rcases p216_3 (m.d 0 2) (by simp) with h242 | h242
                          · linarith only [h242, hlam, p216_0]
                          · rcases p216_3 (m.d 1 2) (by simp) with h244 | h244
                            · linarith only [h208, h244, hlam]
                            · rcases p216_3 (m.d 2 3) (by simp) with h246 | h246
                              · rcases p216_3 (m.d 2 4) (by simp) with h247 | h247
                                · rcases p216_3 (m.d 2 5) (by simp) with h248 | h248
                                  · linarith only [h214, h248, hlam]
                                  · linarith only [h159, h248, hlam]
                                · linarith only [h247, hlam, p216_0]
                              · linarith only [h1, h246, hlam]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          rcases p216_3 (m.d 0 2) (by simp) with h253 | h253
                          · linarith only [h112, h253, hlam]
                          · linarith only [h0, h253, hlam]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h212, hlam, p216_1]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [hlam, p216_0]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h0, h159, hc12, hc24, hlam, hphi, p216_1]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p216_1, u5elo2]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p216_1, u5elo2]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h213, hlam, p216_1]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [h214, hlam, p216_0]
                        · have p216_0 := h216c.1
                          have p216_1 := h216c.2.1
                          have p216_2 := h216c.2.2.1
                          have p216_3 := h216c.2.2.2
                          linarith only [hlam, p216_0]
                      · linarith only [h215, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h0, h112, h214, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h206, h213, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h267 | h267
                  · linarith only [h212, h267, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h267, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h270 | h270
    · rcases m.htr 0 2 4 (by decide) (by decide) with h271 | h271
      · rcases m.htr 0 2 5 (by decide) (by decide) with h272 | h272
        · rcases m.htr 1 2 3 (by decide) (by decide) with h273 | h273
          · rcases m.htr 1 2 4 (by decide) (by decide) with h274 | h274
            · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
              · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h278 | h278
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h279 | h279
                      · rcases h2bigk with h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h0, hlam, p280_1]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h276, h279, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p280_1, u3ehi4]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          rcases p280_3 (m.d 0 2) (by simp) with h284 | h284
                          · rcases p280_3 (m.d 1 2) (by simp) with h285 | h285
                            · rcases p280_3 (m.d 2 3) (by simp) with h286 | h286
                              · linarith only [h270, h286, hlam]
                              · linarith only [h276, h286, hlam]
                            · linarith only [h274, h285, hlam]
                          · linarith only [h284, hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          rcases p280_3 (m.d 0 2) (by simp) with h291 | h291
                          · rcases p280_3 (m.d 1 2) (by simp) with h292 | h292
                            · rcases p280_3 (m.d 2 3) (by simp) with h293 | h293
                              · linarith only [h270, h293, hlam]
                              · linarith only [h277, h293, hlam]
                            · linarith only [h275, h292, hlam]
                          · linarith only [h291, hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h270, h276, h279, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p280_1, u3ehi4]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h276, h279, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p280_1, u3ehi4]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          rcases p280_3 (m.d 0 2) (by simp) with h301 | h301
                          · linarith only [h0, h301, hlam]
                          · linarith only [h271, h301, hlam]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          rcases p280_3 (m.d 0 2) (by simp) with h304 | h304
                          · linarith only [h0, h304, hlam]
                          · linarith only [h272, h304, hlam]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h270, hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h273, hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h270, h277, h278, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p280_1, u3ehi4]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h0, h270, h277, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p280_1, u3ehi4]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h271, hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h274, hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h276, hlam, p280_1]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h0, h271, h277, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p280_1, u3ehi4]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h272, hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h275, hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h277, hlam, p280_1]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [h278, hlam, p280_0]
                        · have p280_0 := h280c.1
                          have p280_1 := h280c.2.1
                          have p280_2 := h280c.2.2.1
                          have p280_3 := h280c.2.2.2
                          linarith only [hlam, p280_0]
                      · linarith only [h279, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h276, h278, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h277, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h325 | h325
                  · linarith only [h276, h325, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h325, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h0, h275, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h271, h274, hlam]
          · linarith only [h0, h270, h273, hlam]
        · linarith only [h270, h272, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h332 | h332
        · rcases m.htr 1 2 3 (by decide) (by decide) with h333 | h333
          · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
            · linarith only [h270, h271, h334, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h336 | h336
              · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                · linarith only [h0, h270, h334, h337, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h270, h334, h337, hc34, hlam, hphi, u3ehi2]
              · linarith only [h0, h332, h336, hlam]
          · linarith only [h0, h270, h333, hlam]
        · linarith only [h270, h332, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h343 | h343
      · rcases m.htr 0 2 5 (by decide) (by decide) with h344 | h344
        · rcases m.htr 1 2 3 (by decide) (by decide) with h345 | h345
          · rcases m.htr 1 2 4 (by decide) (by decide) with h346 | h346
            · rcases m.htr 1 2 5 (by decide) (by decide) with h347 | h347
              · rcases m.htr 2 3 4 (by decide) (by decide) with h348 | h348
                · linarith only [h270, h343, h345, h348, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h270, h343, h348, hlam]
              · linarith only [h270, h344, h347, hc12, hc23, hlam, hphi]
            · linarith only [h270, h343, h345, h346, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h353 | h353
            · rcases m.htr 1 2 5 (by decide) (by decide) with h354 | h354
              · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                · rcases m.htr 2 3 5 (by decide) (by decide) with h356 | h356
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h357 | h357
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h358 | h358
                      · rcases h2bigk with h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h0, hlam, p359_1]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h270, hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h0, h345, h356, h357, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p359_1, u3ehi4]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h0, h345, h356, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p359_1, u3ehi4]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h345, hc02, hc23, hlam, hphi, p359_1]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h345, hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h345, h356, h357, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p359_1, u3ehi4]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h345, h356, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p359_1, u3ehi4]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h343, h356, h357, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p359_1, u3ehi4]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p359_1]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          rcases p359_3 (m.d 0 2) (by simp) with h373 | h373
                          · linarith only [h270, h373, hlam]
                          · linarith only [h343, h373, hlam]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          rcases p359_3 (m.d 0 2) (by simp) with h376 | h376
                          · linarith only [h270, h376, hlam]
                          · linarith only [h344, h376, hlam]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h343, hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h353, hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h355, hlam, p359_1]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h343, h356, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p359_1, u3ehi4]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h344, hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h354, hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h356, hlam, p359_1]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [h357, hlam, p359_0]
                        · have p359_0 := h359c.1
                          have p359_1 := h359c.2.1
                          have p359_2 := h359c.2.2.1
                          have p359_3 := h359c.2.2.2
                          linarith only [hlam, p359_0]
                      · linarith only [h358, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h355, h357, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h0, h345, h356, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h345, h355, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h344, h354, hlam]
            · linarith only [h0, h343, h353, hlam]
        · linarith only [h343, h344, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h396 | h396
        · rcases m.htr 1 2 3 (by decide) (by decide) with h397 | h397
          · rcases m.htr 1 2 4 (by decide) (by decide) with h398 | h398
            · rcases m.htr 1 2 5 (by decide) (by decide) with h399 | h399
              · rcases m.htr 2 3 4 (by decide) (by decide) with h400 | h400
                · rcases m.htr 2 3 5 (by decide) (by decide) with h401 | h401
                  · linarith only [h270, h396, h397, h401, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h343, h400, h401, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h404 | h404
                  · linarith only [h400, h404, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h404, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h270, h396, h399, hc12, hc23, hlam, hphi]
            · linarith only [h270, h397, h398, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h409 | h409
            · linarith only [h343, h396, h397, h409, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h411 | h411
              · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h414 | h414
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h415 | h415
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
                          linarith only [h270, hlam, p416_0]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h343, hlam, p416_0]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h0, h409, h412, h413, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p416_1, u3ehi4]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h409, h412, hc02, hc23, hlam, hphi, p416_1]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [hlam, p416_0]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h397, hlam, p416_0]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h409, hlam, p416_0]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h409, h412, h413, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p416_1, u3ehi4]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h396, h413, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p416_1, u3ehi4]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p416_1]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [hlam, p416_0]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h343, h396, h413, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p416_1, u3ehi4]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          rcases p416_3 (m.d 0 2) (by simp) with h431 | h431
                          · linarith only [h270, h431, hlam]
                          · linarith only [h396, h431, hlam]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h396, h413, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p416_1, u3ehi4]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h0, h396, h413, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p416_1, u3ehi4]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h412, hlam, p416_1]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [hlam, p416_0]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          rcases p416_3 (m.d 0 2) (by simp) with h438 | h438
                          · linarith only [h343, h438, hlam]
                          · linarith only [h396, h438, hlam]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h396, hlam, p416_0]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h411, hlam, p416_0]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h413, hlam, p416_1]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [h414, hlam, p416_0]
                        · have p416_0 := h416c.1
                          have p416_1 := h416c.2.1
                          have p416_2 := h416c.2.2.1
                          have p416_3 := h416c.2.2.2
                          linarith only [hlam, p416_0]
                      · linarith only [h415, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h343, h396, h413, h414, hlam, hphi, ht34, ht45, u3ehi4, u5elo4]
                  · linarith only [h413, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h0, h397, h412, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h396, h411, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h451 | h451
          · rcases m.htr 1 2 4 (by decide) (by decide) with h452 | h452
            · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
              · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
                · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h457 | h457
                      · rcases h2bigk with h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, hlam, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h270, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h343, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h396, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          rcases p458_3 (m.d 0 2) (by simp) with h464 | h464
                          · linarith only [h0, h464, hlam]
                          · rcases p458_3 (m.d 1 2) (by simp) with h466 | h466
                            · rcases p458_3 (m.d 2 3) (by simp) with h467 | h467
                              · linarith only [h451, h467, hlam]
                              · linarith only [h270, h467, hlam]
                            · linarith only [h0, h466, hlam]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h454, h457, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h343, hc01, hc12, hlam, hphi, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h396, hc01, hc12, hlam, hphi, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h451, hc01, hc12, hlam, hphi, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h451, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h343, h451, hc01, hc12, hlam, hphi, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h396, h451, hc01, hc12, hlam, hphi, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h452, hc01, hc12, hlam, hphi, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h452, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h454, hlam, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h396, h451, h454, hc01, hc12, hlam, hphi, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h453, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p458_1, u5elo1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h453, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h455, hlam, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h456, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [hlam, p458_0]
                      · linarith only [h457, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h0, h343, h456, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h455, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h493 | h493
                  · linarith only [h454, h493, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h493, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h0, h453, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h270, h451, h452, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h498 | h498
            · linarith only [h0, h343, h451, h498, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
              · linarith only [h0, h396, h451, h500, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h500, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

end R2N4
