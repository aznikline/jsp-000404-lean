import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_R_L_I_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · linarith only [h0, h4, h7, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h3, h6, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
              · linarith only [h1, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · linarith only [h0, h14, h15, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h13, h14, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
              · linarith only [h1, h13, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h20 | h20
            · linarith only [h20, h3, h4, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
              · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h24, h4, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                      · linarith only [h0, h22, h27, h4, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                        · linarith only [h2, h20, h29, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                          · linarith only [h29, h3, h31, h4, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
                          · rcases h3bigk with h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h31, h4, hc13, hc45, hlam, hphi, ht34, p33_1]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h26, h31, h4, hc45, hlam, hphi, ht23, ht34, p33_1, u2ehi3]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h31, h4, hc34, hc45, hlam, hphi, p33_1]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h4, hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h0, hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h0, h26, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p33_1, u0elo0, u2ehi3]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p33_1, u0elo0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h24, hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h1, hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h22, hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p33_1, u0elo1]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h27, hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h3, hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h23, hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h26, hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [hlam, p33_0]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h31, hlam, p33_1]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h1, h31, hc45, hlam, hphi, ht23, ht34, p33_1, u2ehi2]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h22, h31, hc45, hlam, hphi, ht23, ht34, p33_1, u2ehi2]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [h26, h31, hc45, hlam, hphi, ht23, ht34, p33_1, u2ehi3]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              rcases p33_3 (m.d 0 3) (by simp) with h57 | h57
                              · linarith only [h4, h57, hlam]
                              · linarith only [h3, h57, hlam]
                            · have p33_0 := h33c.1
                              have p33_1 := h33c.2.1
                              have p33_2 := h33c.2.2.1
                              have p33_3 := h33c.2.2.2
                              linarith only [hlam, p33_0]
                    · linarith only [h26, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                · linarith only [h23, h3, h4, hc13, hc35, hlam, hphi]
              · linarith only [h1, h22, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h64 | h64
          · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
            · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
              · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
                · linarith only [h3, h64, h67, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h69 | h69
                  · linarith only [h0, h69, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · linarith only [h3, h64, h69, hc13, hc34, hlam, hphi]
              · linarith only [h1, h66, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h3, h64, h65, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h74 | h74
            · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                · linarith only [h0, h3, h76, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                  · linarith only [h0, h64, h78, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                    · linarith only [h0, h2, h3, h64, h75, h80, hc35, hlam, hphi, ht23, u2ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                      · linarith only [h0, h64, h75, h82, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h84 | h84
                        · linarith only [h2, h84, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · linarith only [h74, h84, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
              · linarith only [h1, h75, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                · linarith only [h0, h3, h89, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h91 | h91
                  · linarith only [h0, h64, h91, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                    · linarith only [h0, h3, h88, h93, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                      · linarith only [h0, h64, h88, h95, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                        · linarith only [h2, h74, h97, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                          · linarith only [h0, h3, h74, h88, h99, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h0, h3, h88, h99, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h1, h88, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
      · linarith only [h1, h2, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h104 | h104
      · linarith only [h1, h104, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h106 | h106
        · rcases m.htr 0 3 5 (by decide) (by decide) with h107 | h107
          · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
            · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
              · linarith only [h0, h1, h109, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
                  · linarith only [h0, h112, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · linarith only [h107, h111, h112, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h0, h106, h109, h111, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
              · linarith only [h0, h1, h116, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                  · linarith only [h0, h119, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · linarith only [h107, h118, h119, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h0, h106, h116, h118, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h123 | h123
            · linarith only [h106, h107, h123, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h125 | h125
              · linarith only [h0, h1, h125, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
                · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                  · linarith only [h0, h128, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                      · linarith only [h1, h107, h131, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h1, h131, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h1, h127, h130, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                · linarith only [h106, h107, h127, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h136 | h136
          · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
            · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
              · linarith only [h0, h1, h138, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                · linarith only [h0, h106, h140, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h142 | h142
                  · linarith only [h0, h142, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · linarith only [h106, h136, h142, hc13, hc34, hlam, hphi]
            · linarith only [h106, h136, h137, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
            · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
              · linarith only [h0, h1, h147, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                · linarith only [h0, h106, h149, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
                  · linarith only [h0, h136, h151, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                    · linarith only [h0, h106, h147, h153, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h1, h153, hc34, hlam, hphi, ht23, u2ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
              · linarith only [h0, h1, h136, h156, hc35, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
                · linarith only [h0, h106, h158, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                  · linarith only [h0, h160, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                    · linarith only [h1, h106, h162, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1, h162, hc34, hlam, hphi, ht23, u2ehi0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h165 | h165
    · rcases m.htr 0 2 4 (by decide) (by decide) with h166 | h166
      · rcases m.htr 0 3 4 (by decide) (by decide) with h167 | h167
        · rcases m.htr 0 3 5 (by decide) (by decide) with h168 | h168
          · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
            · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
              · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                      · linarith only [h165, h174, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                      · linarith only [h168, h173, h174, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h165, h167, h173, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h168, h172, hlam]
                · linarith only [h0, h167, h171, hlam]
              · linarith only [h165, h170, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
              · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                      · linarith only [h165, h185, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                      · linarith only [h165, h168, h184, h185, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h165, h167, h184, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h168, h183, hlam]
                · linarith only [h0, h167, h182, hlam]
              · linarith only [h165, h181, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h192 | h192
            · linarith only [h167, h168, h192, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
              · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
                · rcases m.htr 1 3 5 (by decide) (by decide) with h196 | h196
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                      · linarith only [h165, h168, h198, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                        · linarith only [h166, h192, h200, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h202 | h202
                          · linarith only [h166, h192, h197, h202, hc23, hlam, hphi, u2ehi3]
                          · rcases h3bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h0, hlam, p204_1]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h197, hc34, hlam, hphi, ht0b, ht45, ht5b, p204_1, u0elo2]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h168, h202, hc34, hc45, hlam, hphi, p204_1]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h168, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              rcases p204_3 (m.d 0 3) (by simp) with h210 | h210
                              · linarith only [h0, h210, hlam]
                              · rcases p204_3 (m.d 1 3) (by simp) with h212 | h212
                                · rcases p204_3 (m.d 2 3) (by simp) with h213 | h213
                                  · linarith only [h194, h213, hlam]
                                  · rcases p204_3 (m.d 3 4) (by simp) with h215 | h215
                                    · linarith only [h195, h215, hlam]
                                    · rcases p204_3 (m.d 3 5) (by simp) with h217 | h217
                                      · linarith only [h196, h217, hlam]
                                      · linarith only [h168, h217, hlam]
                                · linarith only [h0, h212, hlam]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              rcases p204_3 (m.d 0 3) (by simp) with h222 | h222
                              · linarith only [h0, h222, hlam]
                              · linarith only [h165, h222, hlam]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h167, h168, h196, hlam, p204_2]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h166, h167, h168, h194, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p204_1, u2ehi3]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h165, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h194, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h165, hc34, hlam, hphi, ht0b, ht45, ht5b, p204_1, u0elo1]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h198, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h167, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h195, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h197, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h202, hlam, p204_1]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h166, h167, hc35, hlam, hphi, ht23, p204_1, u2ehi3]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h196, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h194, h196, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p204_1, u2ehi2]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              rcases p204_3 (m.d 0 3) (by simp) with h240 | h240
                              · linarith only [h168, h240, hlam]
                              · linarith only [h167, h240, hlam]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hlam, p204_0]
                    · linarith only [h167, h197, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                      · linarith only [h0, h196, h246, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                        · linarith only [h166, h248, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h250 | h250
                          · linarith only [h165, h192, h245, h250, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases h3bigk with h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h0, hlam, p252_1]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h0, h196, h250, hc23, hc45, hlam, hphi, ht34, p252_1]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h0, h196, h250, hc34, hc45, hlam, hphi, p252_1]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h168, hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h196, h250, hc03, hc45, hlam, hphi, ht34, p252_1]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h196, h245, h250, hc45, hlam, hphi, ht23, ht34, p252_1, u2ehi3]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h196, h250, hc34, hc45, hlam, hphi, p252_1]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h196, hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h165, hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h194, hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h0, h165, h196, h250, hc34, hc45, hlam, hphi, p252_1]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h246, hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h167, hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h195, hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h245, hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [hlam, p252_0]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h250, hlam, p252_1]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h165, h250, hc45, hlam, hphi, ht23, ht34, p252_1, u2ehi2]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h0, h250, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p252_1]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [h245, h250, hc45, hlam, hphi, ht23, ht34, p252_1, u2ehi3]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              rcases p252_3 (m.d 0 3) (by simp) with h276 | h276
                              · linarith only [h168, h276, hlam]
                              · linarith only [h167, h276, hlam]
                            · have p252_0 := h252c.1
                              have p252_1 := h252c.2.1
                              have p252_2 := h252c.2.2.1
                              have p252_3 := h252c.2.2.2
                              linarith only [hlam, p252_0]
                    · linarith only [h167, h245, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                · linarith only [h0, h167, h195, hlam]
              · linarith only [h165, h194, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h283 | h283
          · rcases m.htr 0 4 5 (by decide) (by decide) with h284 | h284
            · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
              · rcases m.htr 1 3 4 (by decide) (by decide) with h286 | h286
                · linarith only [h167, h283, h286, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h288 | h288
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h289 | h289
                    · linarith only [h165, h286, h289, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h291 | h291
                      · linarith only [h166, h289, h291, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                      · linarith only [h0, h283, h286, h291, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h283, h288, hlam]
              · linarith only [h165, h285, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h167, h283, h284, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h297 | h297
            · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
              · rcases m.htr 1 3 4 (by decide) (by decide) with h299 | h299
                · rcases m.htr 1 3 5 (by decide) (by decide) with h300 | h300
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
                    · linarith only [h165, h167, h301, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                      · linarith only [h165, h283, h303, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                        · linarith only [h166, h305, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · linarith only [h297, h305, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                  · linarith only [h165, h167, h299, h300, hc35, hlam, hphi, ht23, u2ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h309 | h309
                  · linarith only [h165, h283, h299, h309, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                    · linarith only [h0, h165, h299, h311, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h313 | h313
                      · linarith only [h0, h165, h309, h313, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h315 | h315
                        · linarith only [h166, h315, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · linarith only [h166, h297, h315, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
              · linarith only [h165, h298, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h319 | h319
              · rcases m.htr 1 3 4 (by decide) (by decide) with h320 | h320
                · rcases m.htr 1 3 5 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                    · linarith only [h165, h167, h322, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h324 | h324
                      · linarith only [h165, h167, h319, h320, h324, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h326 | h326
                        · linarith only [h166, h297, h326, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h328 | h328
                          · linarith only [h165, h167, h297, h319, h320, h328, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h165, h167, h328, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h165, h167, h320, h321, hc35, hlam, hphi, ht23, u2ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
                  · linarith only [h165, h283, h320, h332, hc34, hlam, hphi, ht23, u2ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
                    · linarith only [h0, h165, h320, h334, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                      · linarith only [h165, h283, h336, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h338 | h338
                        · linarith only [h166, h297, h338, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h340 | h340
                          · linarith only [h165, h167, h297, h340, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h165, h167, h340, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h165, h167, h319, hc34, hlam, hphi, ht23, u2ehi1]
      · linarith only [h165, h166, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h345 | h345
      · linarith only [h165, h345, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h347 | h347
        · rcases m.htr 0 3 5 (by decide) (by decide) with h348 | h348
          · rcases m.htr 0 4 5 (by decide) (by decide) with h349 | h349
            · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
              · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                · rcases m.htr 1 3 5 (by decide) (by decide) with h352 | h352
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h354 | h354
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
                          · linarith only [h165, h347, h350, h356, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases h3bigk with h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h0, hlam, p358_1]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h165, hlam, p358_1]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              rcases p358_3 (m.d 0 3) (by simp) with h362 | h362
                              · rcases p358_3 (m.d 1 3) (by simp) with h363 | h363
                                · rcases p358_3 (m.d 2 3) (by simp) with h364 | h364
                                  · rcases p358_3 (m.d 3 4) (by simp) with h365 | h365
                                    · linarith only [h365, hlam, p358_0]
                                    · rcases p358_3 (m.d 3 5) (by simp) with h367 | h367
                                      · linarith only [h348, h367, hlam]
                                      · linarith only [h356, h367, hlam]
                                  · linarith only [h353, h364, hlam]
                                · linarith only [h351, h363, hlam]
                              · linarith only [h362, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h165, h350, hc12, hlam, hphi, ht01, ht0b, ht5b, p358_1, u5ehi3]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h347, h349, h356, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p358_1]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h345, h350, h353, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p358_1, u2ehi0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              rcases p358_3 (m.d 0 3) (by simp) with h377 | h377
                              · linarith only [h0, h377, hlam]
                              · linarith only [h347, h377, hlam]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              rcases p358_3 (m.d 0 3) (by simp) with h380 | h380
                              · linarith only [h0, h380, hlam]
                              · linarith only [h348, h380, hlam]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h347, h349, h356, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p358_1]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h350, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              rcases p358_3 (m.d 0 3) (by simp) with h386 | h386
                              · linarith only [h165, h386, hlam]
                              · linarith only [h347, h386, hlam]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h350, hc12, hlam, hphi, ht01, ht0b, ht5b, p358_1, u5ehi3]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h347, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h351, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h353, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h356, hlam, p358_1]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h348, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h352, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h354, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h348, hc34, hlam, hphi, ht0b, ht45, ht5b, p358_1, u0elo2]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hlam, p358_0]
                        · linarith only [h345, h349, h355, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi0]
                      · linarith only [h165, h348, h354, hlam]
                    · linarith only [h165, h353, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h0, h348, h352, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h165, h347, h350, h351, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h405 | h405
                · rcases m.htr 1 3 5 (by decide) (by decide) with h406 | h406
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h407 | h407
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h408 | h408
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h409 | h409
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h410 | h410
                          · linarith only [h347, h410, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                          · rcases h3bigk with h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h0, hlam, p412_1]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h165, hlam, p412_1]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              rcases p412_3 (m.d 0 3) (by simp) with h416 | h416
                              · rcases p412_3 (m.d 1 3) (by simp) with h417 | h417
                                · rcases p412_3 (m.d 2 3) (by simp) with h418 | h418
                                  · rcases p412_3 (m.d 3 4) (by simp) with h419 | h419
                                    · linarith only [h419, hlam, p412_0]
                                    · rcases p412_3 (m.d 3 5) (by simp) with h421 | h421
                                      · linarith only [h348, h421, hlam]
                                      · linarith only [h410, h421, hlam]
                                  · linarith only [h407, h418, hlam]
                                · linarith only [h405, h417, hlam]
                              · linarith only [h416, hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [hlam, hphi, ht0b, ht5b, p412_1, u0elo2, u5ehi3]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h347, h349, h350, h410, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p412_1]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h350, hlam, p412_1]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              rcases p412_3 (m.d 0 3) (by simp) with h431 | h431
                              · linarith only [h0, h431, hlam]
                              · linarith only [h347, h431, hlam]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              rcases p412_3 (m.d 0 3) (by simp) with h434 | h434
                              · linarith only [h0, h434, hlam]
                              · linarith only [h348, h434, hlam]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h347, h349, h410, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p412_1]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p412_1]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              rcases p412_3 (m.d 0 3) (by simp) with h440 | h440
                              · linarith only [h165, h440, hlam]
                              · linarith only [h347, h440, hlam]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              rcases p412_3 (m.d 0 3) (by simp) with h443 | h443
                              · linarith only [h165, h443, hlam]
                              · linarith only [h348, h443, hlam]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h347, hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h405, hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h407, hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h410, hlam, p412_1]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h348, hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h406, hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h408, hlam, p412_0]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [h348, hc34, hlam, hphi, ht0b, ht45, ht5b, p412_1, u0elo2]
                            · have p412_0 := h412c.1
                              have p412_1 := h412c.2.1
                              have p412_2 := h412c.2.2.1
                              have p412_3 := h412c.2.2.2
                              linarith only [hlam, p412_0]
                        · linarith only [h345, h349, h409, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi0]
                      · linarith only [h348, h350, h408, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                    · linarith only [h165, h407, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h0, h348, h406, hlam]
                · linarith only [h0, h347, h405, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h461 | h461
              · rcases m.htr 1 3 4 (by decide) (by decide) with h462 | h462
                · rcases m.htr 1 3 5 (by decide) (by decide) with h463 | h463
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h465 | h465
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h466 | h466
                        · linarith only [h345, h349, h461, h464, h466, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h345, h466, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h348, h465, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                    · linarith only [h165, h347, h348, h464, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                  · linarith only [h165, h348, h461, h463, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                · linarith only [h165, h347, h461, h462, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h473 | h473
                · rcases m.htr 1 3 5 (by decide) (by decide) with h474 | h474
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h475 | h475
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h476 | h476
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h477 | h477
                        · linarith only [h345, h349, h477, hc24, hlam, hphi, u2ehi0]
                        · linarith only [h345, h477, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h0, h348, h461, h476, hlam]
                    · linarith only [h347, h461, h475, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                  · linarith only [h0, h348, h474, hlam]
                · linarith only [h0, h347, h473, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h484 | h484
            · linarith only [h347, h348, h484, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h486 | h486
              · rcases m.htr 1 3 4 (by decide) (by decide) with h487 | h487
                · rcases m.htr 1 3 5 (by decide) (by decide) with h488 | h488
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h489 | h489
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h490 | h490
                      · linarith only [h165, h348, h490, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h165, h486, h488, h490, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h165, h347, h348, h486, h488, h489, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h165, h486, h488, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h165, h347, h486, h487, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h496 | h496
                · rcases m.htr 1 3 5 (by decide) (by decide) with h497 | h497
                  · linarith only [h165, h348, h486, h497, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h499 | h499
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h500 | h500
                      · linarith only [h0, h345, h347, h497, h500, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h165, h500, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h165, h347, h499, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                · linarith only [h0, h347, h496, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h505 | h505
          · rcases m.htr 0 4 5 (by decide) (by decide) with h506 | h506
            · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
              · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
                · linarith only [h347, h505, h508, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · linarith only [h165, h507, h508, hc34, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h511 | h511
                · linarith only [h347, h505, h511, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h513 | h513
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                    · linarith only [h0, h511, h514, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h165, h514, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h0, h505, h513, hlam]
            · linarith only [h347, h505, h506, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h519 | h519
            · rcases m.htr 1 2 3 (by decide) (by decide) with h520 | h520
              · rcases m.htr 1 3 4 (by decide) (by decide) with h521 | h521
                · rcases m.htr 1 3 5 (by decide) (by decide) with h522 | h522
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
                    · linarith only [h165, h347, h523, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h165, h520, h521, h523, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h347, h521, h522, hc03, hc35, hlam, hphi]
                · linarith only [h165, h520, h521, hc34, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h528 | h528
                · linarith only [h165, h347, h520, h528, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h530 | h530
                  · linarith only [h165, h505, h528, h530, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h532 | h532
                    · linarith only [h520, h528, h532, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h165, h532, hc34, hlam, hphi, ht23, u2ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
              · rcases m.htr 1 3 4 (by decide) (by decide) with h536 | h536
                · rcases m.htr 1 3 5 (by decide) (by decide) with h537 | h537
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h538 | h538
                    · linarith only [h165, h347, h538, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h165, h535, h536, h538, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h0, h347, h536, h537, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h165, h535, h536, hc34, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h543 | h543
                · linarith only [h165, h347, h535, h543, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h545 | h545
                  · linarith only [h165, h505, h543, h545, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h547 | h547
                    · linarith only [h535, h543, h547, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h165, h547, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_10_12_13_25_L_0_L_R_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h1, h11, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h1, h11, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h1, h10, h4, h6, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                    · linarith only [h1, h5, h9, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                  · linarith only [h3, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h2, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
                · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h2, h21, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                        · linarith only [h1, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h1, h23, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h1, h20, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                  · linarith only [h19, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h18, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h4, h5, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h30 | h30
            · linarith only [h30, h4, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h32 | h32
              · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h0, h30, h35, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                        · linarith only [h1, h38, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                          · linarith only [h1, h30, h40, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                              · rcases h5bigk with h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [hlam, p44_0]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h2, h32, h35, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1, u0elo1, u3ehi1]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h2, h32, h40, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p44_1, u0elo1, u2ehi2]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h30, hlam, p44_1]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht0b, ht5b, p44_1, u0elo4]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h0, hlam, p44_0]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [hlam, p44_0]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h40, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p44_1, u2ehi2]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h35, hlam, p44_1]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p44_1, u0elo0]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h3, hlam, p44_1]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h34, hlam, p44_1]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [hlam, p44_0]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h40, hlam, p44_1]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h3, hc45, hlam, hphi, ht0b, ht5b, p44_1, u0elo1]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h3, hc35, hlam, hphi, ht23, p44_1, u2ehi4]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h34, hc35, hlam, hphi, ht23, p44_1, u2ehi4]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [hc35, hlam, hphi, ht23, p44_1, u2ehi4]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [hlam, p44_0]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  rcases p44_3 (m.d 0 5) (by simp) with h64 | h64
                                  · linarith only [h30, h64, hlam]
                                  · linarith only [h32, h64, hlam]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h32, hlam, p44_0]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h37, hlam, p44_0]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h42, hlam, p44_0]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [h43, hlam, p44_0]
                                · have p44_0 := h44c.1
                                  have p44_1 := h44c.2.1
                                  have p44_2 := h44c.2.2.1
                                  have p44_3 := h44c.2.2.2
                                  linarith only [hlam, p44_0]
                              · linarith only [h1, h4, h43, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h2, h32, h42, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                      · linarith only [h2, h32, h33, h37, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                  · linarith only [h3, h34, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h2, h33, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                    · linarith only [h0, h1, h30, h79, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                      · linarith only [h0, h2, h32, h81, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                        · linarith only [h1, h4, h83, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                          · linarith only [h1, h79, h85, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                            · linarith only [h2, h32, h87, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                              · linarith only [h2, h32, h89, hc34, hlam, hphi, ht23, u2ehi3]
                              · linarith only [h1, h4, h89, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h3, h78, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h2, h77, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · linarith only [h2, h3, hc25, hlam, hphi, u2ehi3]
      · linarith only [h1, h2, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h96 | h96
      · linarith only [h1, h96, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h98 | h98
        · linarith only [h1, h98, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h100 | h100
          · rcases m.htr 0 3 5 (by decide) (by decide) with h101 | h101
            · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
              · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                  · linarith only [h0, h104, h98, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                  · linarith only [h103, h104, hc25, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                  · linarith only [h103, h107, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h112 | h112
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h113 | h113
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h114 | h114
                              · rcases h5bigk with h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h102, h107, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p115_1, u0elo3, u2ehi1]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h98, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hc35, hlam, hphi, ht0b, ht5b, p115_1, u0elo4]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h100, h102, hc45, hlam, hphi, ht0b, ht5b, p115_1, u0elo2]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h0, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h107, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h110, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p115_1, u3ehi4]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p115_1, u0elo0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h98, hc25, hlam, hphi, p115_1, u2ehi0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h107, hc25, hlam, hphi, p115_1, u2ehi1]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h112, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p115_1, u3ehi4]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  rcases p115_3 (m.d 0 5) (by simp) with h130 | h130
                                  · linarith only [h130, h98, hlam]
                                  · linarith only [h102, h130, hlam]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h101, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h109, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h112, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h109, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p115_1]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h102, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h110, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h113, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h114, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hlam, p115_0]
                              · linarith only [h100, h102, h114, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                            · linarith only [h100, h102, h113, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
                          · linarith only [h0, h109, h112, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                        · linarith only [h1, h111, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h102, h103, h110, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                    · linarith only [h101, h109, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
                · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                  · linarith only [h0, h150, h98, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                  · linarith only [h149, h150, h96, hc25, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                  · linarith only [h149, h153, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h155 | h155
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                      · linarith only [h102, h149, h156, h96, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h159 | h159
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                            · linarith only [h102, h158, h160, h96, hc23, hlam, hphi, u2ehi0]
                            · linarith only [h160, h96, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h0, h155, h159, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                        · linarith only [h1, h158, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h101, h155, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
            · linarith only [h100, h101, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h167 | h167
            · linarith only [h100, h167, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
              · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
                · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
                  · linarith only [h0, h171, h98, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                  · linarith only [h170, h171, hc25, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                  · linarith only [h170, h174, h98, hc24, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h176 | h176
                    · linarith only [h0, h167, h176, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h178 | h178
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
                        · linarith only [h1, h100, h179, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1, h179, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h169, h170, h178, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h183 | h183
                · rcases m.htr 1 2 5 (by decide) (by decide) with h184 | h184
                  · linarith only [h0, h184, h98, hlam]
                  · linarith only [h183, h184, hc25, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h187 | h187
                  · linarith only [h183, h187, h98, hc24, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h189 | h189
                    · linarith only [h0, h1, h167, h189, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h191 | h191
                      · linarith only [h169, h183, h191, h96, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                        · linarith only [h1, h100, h193, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1, h193, hc34, hlam, hphi, ht23, u2ehi0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h196 | h196
    · rcases m.htr 0 2 4 (by decide) (by decide) with h197 | h197
      · rcases m.htr 0 2 5 (by decide) (by decide) with h198 | h198
        · rcases m.htr 0 3 4 (by decide) (by decide) with h199 | h199
          · rcases m.htr 0 3 5 (by decide) (by decide) with h200 | h200
            · rcases m.htr 0 4 5 (by decide) (by decide) with h201 | h201
              · rcases m.htr 1 2 4 (by decide) (by decide) with h202 | h202
                · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                        · linarith only [h196, h206, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h199, h206, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                      · linarith only [h201, h202, h205, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                    · linarith only [h196, h200, h204, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                  · linarith only [h198, h203, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h197, h202, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
                · rcases m.htr 1 2 5 (by decide) (by decide) with h214 | h214
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h215 | h215
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h216 | h216
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h217 | h217
                        · linarith only [h196, h217, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h196, h199, h217, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
                        · linarith only [h196, h220, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h196, h199, h220, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h196, h200, h215, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                  · linarith only [h198, h214, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h197, h213, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h199, h200, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h227 | h227
            · linarith only [h199, h227, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h229 | h229
              · rcases m.htr 1 2 4 (by decide) (by decide) with h230 | h230
                · rcases m.htr 1 2 5 (by decide) (by decide) with h231 | h231
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h232 | h232
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h233 | h233
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                        · linarith only [h196, h234, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                          · linarith only [h196, h227, h236, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h238 | h238
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h239 | h239
                              · rcases h5bigk with h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h0, hlam, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h229, hc25, hlam, hphi, ht0b, ht5b, p240_1, u0elo3]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h227, hlam, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h197, h229, hc45, hlam, hphi, ht0b, ht5b, p240_1, u0elo1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h0, h230, h233, hc01, hc12, hlam, hphi, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h230, h233, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p240_1, u2ehi4]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h227, h230, h233, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p240_1, u3ehi0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  rcases p240_3 (m.d 0 5) (by simp) with h250 | h250
                                  · linarith only [h0, h250, hlam]
                                  · linarith only [h229, h250, hlam]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h198, hlam, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h231, hlam, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h236, hlam, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h198, hc45, hlam, hphi, ht0b, ht5b, p240_1, u0elo1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h198, h239, hc34, hlam, hphi, ht23, p240_1, u2ehi4]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h232, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h232, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p240_1, u2ehi4]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h232, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h229, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h233, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h238, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h239, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [hlam, p240_0]
                              · linarith only [h196, h199, h239, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h197, h229, h238, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                      · linarith only [h197, h229, h230, h233, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h271 | h271
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                        · linarith only [h196, h199, h229, h272, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h274 | h274
                          · linarith only [h196, h232, h274, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h276 | h276
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                              · rcases h5bigk with h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [hlam, p278_0]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h0, hlam, p278_1]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h229, hc25, hlam, hphi, ht0b, ht5b, p278_1, u0elo3]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h227, hlam, p278_1]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h197, h229, hc45, hlam, hphi, ht0b, ht5b, p278_1, u0elo1]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h0, h232, hc01, hc35, hlam, hphi, ht12, ht23, p278_1]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [hlam, p278_0]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h232, hc35, hlam, hphi, ht23, p278_1, u2ehi4]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h232, hlam, p278_1]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  rcases p278_3 (m.d 0 5) (by simp) with h288 | h288
                                  · linarith only [h0, h288, hlam]
                                  · linarith only [h229, h288, hlam]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h198, hlam, p278_1]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h231, hlam, p278_1]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [hlam, p278_0]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h274, hlam, p278_1]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h198, hc45, hlam, hphi, ht0b, ht5b, p278_1, u0elo1]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h198, h277, hc34, hlam, hphi, ht23, p278_1, u2ehi4]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h0, h277, hc01, hc34, hlam, hphi, ht12, ht23, p278_1]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h277, hc34, hlam, hphi, ht23, p278_1, u2ehi4]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [hlam, p278_0]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  rcases p278_3 (m.d 0 5) (by simp) with h300 | h300
                                  · linarith only [h227, h300, hlam]
                                  · linarith only [h229, h300, hlam]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h229, hlam, p278_0]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h271, hlam, p278_0]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h276, hlam, p278_0]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [h277, hlam, p278_0]
                                · have p278_0 := h278c.1
                                  have p278_1 := h278c.2.1
                                  have p278_2 := h278c.2.2.1
                                  have p278_3 := h278c.2.2.2
                                  linarith only [hlam, p278_0]
                              · linarith only [h196, h199, h277, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h197, h229, h276, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                      · linarith only [h197, h229, h230, h271, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                  · linarith only [h198, h231, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h197, h230, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h313 | h313
                · rcases m.htr 1 2 5 (by decide) (by decide) with h314 | h314
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h315 | h315
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h316 | h316
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
                        · linarith only [h196, h199, h317, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h319 | h319
                          · linarith only [h196, h227, h319, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h321 | h321
                            · linarith only [h197, h229, h321, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h323 | h323
                              · linarith only [h197, h229, h323, hc34, hlam, hphi, ht23, u2ehi3]
                              · linarith only [h196, h199, h313, h316, h323, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                        · linarith only [h196, h199, h326, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h328 | h328
                          · linarith only [h196, h199, h328, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h330 | h330
                            · linarith only [h197, h316, h330, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                              · linarith only [h196, h227, h315, h316, h332, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h196, h199, h332, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h335 | h335
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                        · linarith only [h196, h199, h336, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
                          · linarith only [h196, h199, h229, h313, h315, h335, h338, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h340 | h340
                            · linarith only [h197, h229, h340, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h342 | h342
                              · linarith only [h196, h199, h229, h342, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h196, h199, h313, h335, h342, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h345 | h345
                        · linarith only [h196, h199, h345, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h347 | h347
                          · linarith only [h196, h199, h347, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h349 | h349
                            · linarith only [h197, h335, h349, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h351 | h351
                              · linarith only [h199, h229, h351, hc34, hlam, hphi, u3ehi0]
                              · linarith only [h196, h199, h351, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h198, h314, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h197, h313, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · linarith only [h197, h198, hc25, hlam, hphi, u2ehi3]
      · linarith only [h196, h197, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h358 | h358
      · linarith only [h196, h358, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h360 | h360
        · linarith only [h196, h360, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h362 | h362
          · rcases m.htr 0 3 5 (by decide) (by decide) with h363 | h363
            · rcases m.htr 0 4 5 (by decide) (by decide) with h364 | h364
              · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                · rcases m.htr 1 2 5 (by decide) (by decide) with h366 | h366
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h367 | h367
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h368 | h368
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h369 | h369
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h370 | h370
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h371 | h371
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h372 | h372
                              · rcases h5bigk with h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h0, hlam, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h360, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h364, hlam, hphi, ht0b, ht34, ht45, ht5b, p373_1, u0elo3, u3ehi4]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h360, h365, h371, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h0, h367, hc01, hc13, hlam, hphi, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h365, h368, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p373_1, u2ehi4]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h365, h368, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p373_1, u3ehi4]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  rcases p373_3 (m.d 0 5) (by simp) with h383 | h383
                                  · linarith only [h0, h383, hlam]
                                  · linarith only [h364, h383, hlam]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h360, hc25, hlam, hphi, p373_1, u2ehi0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h366, hlam, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h366, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p373_1, u3ehi4]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h365, h371, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h363, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h367, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h370, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h362, h372, hc45, hlam, hphi, ht0b, ht5b, p373_1, u0elo2]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h364, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h368, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h371, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h372, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                              · linarith only [h358, h364, h365, h372, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h358, h364, h371, hlam]
                          · linarith only [h363, h370, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                        · linarith only [h196, h363, h369, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h362, h364, h365, h368, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
                    · linarith only [h363, h367, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h365, h366, hc25, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h408 | h408
                  · linarith only [h360, h365, h408, hc24, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h410 | h410
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h411 | h411
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h414 | h414
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h415 | h415
                              · rcases h5bigk with h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c
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
                                  linarith only [h360, hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h364, hc35, hlam, hphi, ht0b, ht5b, p416_1, u0elo3]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h362, h364, hc45, hlam, hphi, ht0b, ht5b, p416_1, u0elo2]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h0, h365, h411, h412, hc01, hc23, hlam, hphi, ht12, p416_1]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h408, hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h365, h411, h412, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p416_1, u3ehi4]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  rcases p416_3 (m.d 0 5) (by simp) with h426 | h426
                                  · linarith only [h0, h426, hlam]
                                  · linarith only [h364, h426, hlam]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h360, h412, h414, hc23, hlam, hphi, p416_1, u2ehi0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h0, h412, h414, hc01, hc23, hlam, hphi, ht12, p416_1]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h412, h414, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p416_1, u3ehi4]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  rcases p416_3 (m.d 0 5) (by simp) with h433 | h433
                                  · linarith only [h360, h433, hlam]
                                  · linarith only [h364, h433, hlam]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h363, hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h410, hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h413, hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h410, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p416_1]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h364, hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h411, hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h414, hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [h415, hlam, p416_0]
                                · have p416_0 := h416c.1
                                  have p416_1 := h416c.2.1
                                  have p416_2 := h416c.2.2.1
                                  have p416_3 := h416c.2.2.2
                                  linarith only [hlam, p416_0]
                              · linarith only [h362, h364, h415, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                            · linarith only [h362, h364, h414, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
                          · linarith only [h196, h363, h413, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi0]
                        · linarith only [h196, h363, h412, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h362, h364, h365, h411, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                    · linarith only [h363, h410, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h452 | h452
                · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h454 | h454
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h455 | h455
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h456 | h456
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h457 | h457
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h458 | h458
                            · linarith only [h362, h364, h452, h458, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h358, h458, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h196, h363, h457, hlam]
                        · linarith only [h196, h363, h456, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h358, h452, h455, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h363, h454, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h358, h452, h453, hc25, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h466 | h466
                  · linarith only [h452, h466, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h468 | h468
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h469 | h469
                      · linarith only [h358, h364, h452, h469, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h471 | h471
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h472 | h472
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h473 | h473
                            · linarith only [h358, h364, h471, h473, hc23, hlam, hphi, u2ehi0]
                            · linarith only [h358, h473, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h196, h363, h472, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi0]
                        · linarith only [h196, h362, h363, h471, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                    · linarith only [h363, h468, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
            · linarith only [h362, h363, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h480 | h480
            · linarith only [h362, h480, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h482 | h482
              · rcases m.htr 1 2 4 (by decide) (by decide) with h483 | h483
                · rcases m.htr 1 2 5 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h485 | h485
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h486 | h486
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h487 | h487
                        · linarith only [h196, h362, h487, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h196, h487, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h358, h482, h483, h486, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                        · linarith only [h196, h362, h492, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h196, h492, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h358, h482, h483, h491, hlam]
                  · linarith only [h483, h484, hc25, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h497 | h497
                  · linarith only [h483, h497, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h499 | h499
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h500 | h500
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h501 | h501
                        · linarith only [h196, h362, h501, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h196, h501, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h482, h483, h500, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h505 | h505
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h506 | h506
                        · linarith only [h196, h362, h506, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h196, h506, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h482, h483, h505, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h510 | h510
                · rcases m.htr 1 2 5 (by decide) (by decide) with h511 | h511
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h512 | h512
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h513 | h513
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                        · linarith only [h196, h362, h514, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h196, h514, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h358, h510, h513, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h518 | h518
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
                        · linarith only [h196, h362, h519, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h196, h519, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h358, h510, h518, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h358, h510, h511, hc25, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h524 | h524
                  · linarith only [h510, h524, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h526 | h526
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h527 | h527
                      · linarith only [h358, h482, h510, h527, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h529 | h529
                        · linarith only [h196, h362, h529, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h196, h529, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h532 | h532
                      · linarith only [h196, h362, h482, h510, h532, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h534 | h534
                        · linarith only [h196, h362, h534, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h196, h534, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
