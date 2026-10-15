import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_0_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h7, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                    · linarith only [h8, h9, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h4, h8, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h1, h14, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                    · linarith only [h13, h14, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h13, h4, h7, hc12, hlam, hphi, ht23, u3elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h1, h20, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                    · linarith only [h20, h5, hc13, hlam, hphi, u3elo0]
                  · linarith only [h18, h19, h4, hc23, hlam, hphi, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h1, h25, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                    · linarith only [h25, h5, hc13, hlam, hphi, u3elo0]
                  · linarith only [h18, h24, h4, hc12, hlam, hphi, ht23, u3elo0]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h30 | h30
            · linarith only [h30, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h32 | h32
              · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
                · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                  · linarith only [h1, h30, h34, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                    · linarith only [h1, h30, h36, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
                      · linarith only [h2, h38, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                      · linarith only [h32, h34, h38, h4, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                  · linarith only [h1, h30, h4, h41, hc04, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h43 | h43
                    · linarith only [h1, h30, h43, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
                      · linarith only [h2, h45, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                      · linarith only [h32, h33, h4, h41, h45, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
                  · linarith only [h1, h4, h49, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h51 | h51
                    · linarith only [h1, h4, h51, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                      · linarith only [h2, h32, h53, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                        · linarith only [h0, h48, h55, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                          · linarith only [h2, h30, h32, h48, h49, h57, hlam, hphi, u5ehi5, u5elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                            · linarith only [h32, h4, h59, hc03, hlam, hphi, u3elo3]
                            · linarith only [h1, h4, h48, h59, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                  · linarith only [h1, h4, h62, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
                    · linarith only [h1, h30, h64, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
                      · linarith only [h2, h66, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                        · linarith only [h1, h4, h48, h68, hc12, hlam, hphi, ht23, u3elo2]
                        · linarith only [h48, h68, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h72 | h72
        · rcases m.htr 0 3 4 (by decide) (by decide) with h73 | h73
          · linarith only [h1, h2, h73, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h75 | h75
            · linarith only [h73, h75, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
              · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                · linarith only [h0, h2, h73, h78, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                  · linarith only [h1, h2, h72, h73, h75, h80, hlam, hphi, u5ehi6, u5elo3]
                  · linarith only [h2, h72, h80, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi6]
              · linarith only [h2, h72, h77, hlam, hphi, u5ehi6, u5elo4]
        · linarith only [h0, h72, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h86 | h86
    · rcases m.htr 0 1 4 (by decide) (by decide) with h87 | h87
      · rcases m.htr 0 1 5 (by decide) (by decide) with h88 | h88
        · linarith only [h0, h88, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
        · linarith only [h87, h88, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h91 | h91
        · linarith only [h0, h91, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
        · linarith only [h86, h91, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h94 | h94
      · rcases m.htr 0 1 5 (by decide) (by decide) with h95 | h95
        · linarith only [h86, h95, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi6]
        · linarith only [h94, h95, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h98 | h98
        · linarith only [h0, h98, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h100 | h100
          · rcases m.htr 0 3 5 (by decide) (by decide) with h101 | h101
            · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
              · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                          · linarith only [h103, h108, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                          · linarith only [h101, h108, hc23, hlam, hphi, u3elo0]
                        · linarith only [h100, h107, h86, hc23, hlam, hphi, u3elo1]
                      · linarith only [h102, h106, h94, hlam]
                    · linarith only [h100, h105, h86, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h100, h102, h104, h86, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi9]
                · linarith only [h0, h103, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                      · linarith only [h102, h117, h119, h94, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h119, h94, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h101, h118, hc13, hlam, hphi, u3elo0]
                  · linarith only [h101, h117, h86, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                · linarith only [h0, h116, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h100, h101, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h126 | h126
            · linarith only [h100, h126, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
              · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
                · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
                  · linarith only [h100, h130, hc03, hlam, hphi, u3elo1]
                  · linarith only [h130, h86, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h129, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
                · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
                  · linarith only [h100, h134, h135, h86, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h135, h86, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h134, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_10_12_13_25_L_0_L_0_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · linarith only [h3, h7, hc12, hlam, hphi, u2elo0]
              · linarith only [h5, h6, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11 | h11
              · linarith only [h11, h5, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                · linarith only [h0, h13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · linarith only [h13, h3, hc12, hlam, hphi, u2elo0]
          · linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h17 | h17
          · rcases m.htr 0 3 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                · linarith only [h20, h3, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                    · linarith only [h1, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h18, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h17, h22, h3, hc12, hlam, hphi, u2elo2]
              · linarith only [h18, h19, hc35, hlam, hphi, u3ehi3]
            · linarith only [h17, h18, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h29 | h29
            · rcases m.htr 0 3 5 (by decide) (by decide) with h30 | h30
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                · linarith only [h3, h31, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h0, h17, h33, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                    · linarith only [h1, h35, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h29, h35, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · linarith only [h29, h30, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h39 | h39
              · linarith only [h29, h39, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                · linarith only [h0, h41, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                  · linarith only [h0, h17, h29, h3, h43, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                    · linarith only [h1, h29, h45, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                      · linarith only [h2, h47, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                        · linarith only [h1, h29, h49, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                          · linarith only [h43, h47, h51, hc12, hlam, hphi, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                            · linarith only [h3, h49, h51, h53, hc02, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h29, h53, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h56 | h56
        · rcases m.htr 0 2 4 (by decide) (by decide) with h57 | h57
          · linarith only [h0, h2, h57, hlam]
          · linarith only [h56, h57, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h60 | h60
          · linarith only [h0, h2, h56, h60, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h62 | h62
            · linarith only [h1, h2, h62, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h64 | h64
              · linarith only [h62, h64, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
                · linarith only [h56, h66, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h68 | h68
                  · linarith only [h1, h60, h66, h68, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h1, h2, h68, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h71 | h71
      · rcases m.htr 0 2 3 (by decide) (by decide) with h72 | h72
        · linarith only [h0, h1, h72, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
          · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
            · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
              · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                · linarith only [h0, h72, h77, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h1, h77, hc12, hlam, hphi, u2elo2]
              · linarith only [h75, h76, hc35, hlam, hphi, u3ehi3]
            · linarith only [h0, h1, h74, h75, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h82 | h82
            · rcases m.htr 0 3 5 (by decide) (by decide) with h83 | h83
              · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                · linarith only [h0, h84, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · linarith only [h0, h1, h84, hc12, hlam, hphi, u2elo2]
              · linarith only [h82, h83, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h71, h82, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h89 | h89
        · linarith only [h0, h1, h89, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h91 | h91
          · linarith only [h0, h71, h91, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h93 | h93
            · rcases m.htr 0 3 5 (by decide) (by decide) with h94 | h94
              · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                · linarith only [h89, h95, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1, h95, hc12, hlam, hphi, u2elo2]
              · linarith only [h93, h94, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h99 | h99
              · linarith only [h93, h99, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                · linarith only [h0, h101, h89, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h1, h101, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h104 | h104
    · linarith only [h0, h104, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h106 | h106
      · rcases m.htr 0 2 3 (by decide) (by decide) with h107 | h107
        · rcases m.htr 0 2 4 (by decide) (by decide) with h108 | h108
          · rcases m.htr 0 3 4 (by decide) (by decide) with h109 | h109
            · rcases m.htr 0 3 5 (by decide) (by decide) with h110 | h110
              · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                    · linarith only [h104, h106, h111, h113, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                    · linarith only [h104, h107, h109, h113, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h107, h110, h112, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · linarith only [h0, h107, h110, h111, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
              · linarith only [h109, h110, hc35, hlam, hphi, u3ehi3]
            · linarith only [h104, h106, h109, hlam]
          · linarith only [h107, h108, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h121 | h121
          · rcases m.htr 0 3 4 (by decide) (by decide) with h122 | h122
            · rcases m.htr 0 3 5 (by decide) (by decide) with h123 | h123
              · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                · linarith only [h0, h107, h124, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h106, h122, h124, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
              · linarith only [h122, h123, hc35, hlam, hphi, u3ehi3]
            · linarith only [h104, h106, h122, hlam]
          · linarith only [h0, h106, h121, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h130 | h130
        · rcases m.htr 0 2 4 (by decide) (by decide) with h131 | h131
          · rcases m.htr 0 3 4 (by decide) (by decide) with h132 | h132
            · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
              · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
                · rcases m.htr 1 2 4 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                        · linarith only [h130, h138, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h132, h138, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                        · linarith only [h0, h130, h141, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                        · linarith only [h104, h132, h134, h141, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · linarith only [h104, h132, h136, hlam]
                  · linarith only [h0, h131, h135, hlam]
                · linarith only [h0, h134, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h132, h133, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h148 | h148
              · linarith only [h132, h148, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
                · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                    · linarith only [h130, h132, h150, h152, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                        · linarith only [h104, h130, h152, h155, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                          · linarith only [h0, h131, h157, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                          · linarith only [h151, h154, h155, h157, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                        · linarith only [h104, h152, h160, hc01, hlam, hphi, ht12, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h162 | h162
                          · linarith only [h0, h106, h131, h154, h162, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                            · linarith only [h106, h132, h154, h164, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h130, h132, h164, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h131, h151, hlam]
                · linarith only [h0, h150, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h130, h131, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h170 | h170
          · rcases m.htr 0 3 4 (by decide) (by decide) with h171 | h171
            · rcases m.htr 0 3 5 (by decide) (by decide) with h172 | h172
              · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
                · linarith only [h130, h173, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h173, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h171, h172, hc35, hlam, hphi, u3ehi3]
            · linarith only [h130, h170, h171, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
            · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
              · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
                · linarith only [h130, h180, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h180, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h178, h179, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h184 | h184
              · linarith only [h178, h184, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
                · linarith only [h0, h130, h186, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h186, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_10_12_13_25_L_0_L_R_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h1, h10, h13, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h1, h10, h12, h13, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h12, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                        · linarith only [h11, h3, hc23, hlam, hphi, u3elo0]
                      · linarith only [h10, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h19, h21, h6, h9, hlam, hphi, ht23, u2ehi4, u3elo2]
                          · linarith only [h21, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                        · linarith only [h20, hlam, hphi, ht23, u2ehi2, u3elo4]
                      · linarith only [h19, hlam, hphi, ht23, u2ehi2, u3elo3]
                  · linarith only [h3, h8, hc13, hlam, hphi, u3elo0]
                · linarith only [h5, h7, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h2, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h5, hlam, hphi, ht23, u2ehi1, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
            · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
              · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h0, h31, h32, h34, h4, hlam, hphi, ht23, u2ehi4, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                          · linarith only [h1, h34, h36, h38, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h40 | h40
                            · linarith only [h38, h40, hlam, hphi, ht23, u2ehi3, u3elo3]
                            · rcases h5bigk with h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h31, h38, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p42_1, u0elo4, u2ehi3]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h0, h38, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p42_1, u0elo0, u2ehi3]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h3, h40, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p42_1, u3elo0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h4, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h0, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h38, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p42_1, u2ehi3]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h0, h40, hc34, hlam, hphi, ht0b, ht45, ht5b, p42_1, u0elo0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h34, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h2, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h31, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h2, h40, hc34, hlam, hphi, ht0b, ht45, ht5b, p42_1, u0elo1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h38, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h3, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h33, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h37, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h40, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h2, hc45, hlam, hphi, ht23, ht34, p42_1, u2ehi4]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h31, hc45, hlam, hphi, ht23, ht34, p42_1, u2ehi4]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hc45, hlam, hphi, ht23, ht34, p42_1, u2ehi4]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h40, hc34, hc45, hlam, hphi, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hlam, p42_0]
                        · linarith only [h37, hlam, hphi, ht23, u2ehi2, u3elo4]
                      · linarith only [h36, hlam, hphi, ht23, u2ehi2, u3elo3]
                  · linarith only [h3, h33, hc13, hlam, hphi, u3elo0]
                · linarith only [h30, h32, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h2, h31, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h30, hlam, hphi, ht23, u2ehi1, u3elo2]
        · linarith only [h1, h3, hlam, hphi, ht23, u2ehi2, u3elo4]
      · linarith only [h1, h2, hc25, hlam, hphi, u2ehi2]
    · linarith only [h1, hlam, hphi, ht23, u2ehi0, u3elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h77 | h77
    · rcases m.htr 0 2 5 (by decide) (by decide) with h78 | h78
      · rcases m.htr 0 3 5 (by decide) (by decide) with h79 | h79
        · rcases m.htr 0 4 5 (by decide) (by decide) with h80 | h80
          · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
            · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
              · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
                · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h87 | h87
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h88 | h88
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                            · linarith only [h77, h86, h89, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h77, h86, h88, h89, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h83, h85, h88, hlam, hphi, ht23, u2ehi3, u3elo1]
                        · linarith only [h87, hlam, hphi, ht23, u2ehi2, u3elo4]
                      · linarith only [h86, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h0, h80, h85, hlam]
                  · linarith only [h79, h84, hc13, hlam, hphi, u3elo0]
                · linarith only [h81, h83, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h78, h81, h82, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi2]
            · linarith only [h81, hlam, hphi, ht23, u2ehi1, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h100 | h100
            · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
              · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                    · linarith only [h102, h104, h78, h80, hlam, hphi, ht23, u2ehi4, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h108 | h108
                          · linarith only [h0, h104, h106, h108, h77, h78, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h110 | h110
                            · linarith only [h106, h108, h110, h77, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                            · rcases h5bigk with h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [hlam, p112_0]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h0, hlam, p112_1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h108, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p112_1, u0elo4, u2ehi3]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h110, h79, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p112_1, u3elo0]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h80, hlam, p112_1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p112_1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [hlam, p112_0]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h101, h108, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p112_1, u2ehi3]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h103, h110, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p112_1, u3elo1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h104, hlam, p112_1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h78, hlam, p112_1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h101, hlam, p112_1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [hlam, p112_0]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h107, h110, h77, hc34, hlam, hphi, ht0b, ht45, ht5b, p112_1, u0elo1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h108, hlam, p112_1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h79, hlam, p112_0]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h103, hlam, p112_0]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h107, hlam, p112_0]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [hlam, p112_0]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h110, hlam, p112_1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h108, h78, hc45, hlam, hphi, ht23, ht34, p112_1, u2ehi3]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p112_1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h108, hc45, hlam, hphi, ht23, ht34, p112_1, u2ehi3]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [h110, hc34, hc45, hlam, hphi, p112_1]
                              · have p112_0 := h112c.1
                                have p112_1 := h112c.2.1
                                have p112_2 := h112c.2.2.1
                                have p112_3 := h112c.2.2.2
                                linarith only [hlam, p112_0]
                        · linarith only [h107, hlam, hphi, ht23, u2ehi2, u3elo4]
                      · linarith only [h106, hlam, hphi, ht23, u2ehi2, u3elo3]
                  · linarith only [h103, h79, hc13, hlam, hphi, u3elo0]
                · linarith only [h100, h102, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h101, h78, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h100, hlam, hphi, ht23, u2ehi1, u3elo2]
        · linarith only [h77, h79, hlam, hphi, ht23, u2ehi2, u3elo4]
      · linarith only [h77, h78, hc25, hlam, hphi, u2ehi2]
    · linarith only [h77, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_10_12_13_25_L_0_L_R_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                  · linarith only [h0, h2, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                · linarith only [h0, h2, h3, h5, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
              · linarith only [h0, h2, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
            · linarith only [h1, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · linarith only [h0, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
          · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h19, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                  · linarith only [h0, h19, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h22, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                  · linarith only [h0, h2, h22, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
              · linarith only [h0, h17, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
            · linarith only [h15, h16, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h15, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
            · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
              · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h0, h2, h33, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h1, h35, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                    · linarith only [h28, h35, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                · linarith only [h2, h28, h31, h32, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                  · linarith only [h0, h31, h40, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                    · linarith only [h1, h42, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                    · linarith only [h1, h28, h42, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                · linarith only [h1, h28, h30, h39, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
            · linarith only [h1, h30, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · linarith only [h0, h29, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
          · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
            · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
              · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                  · linarith only [h0, h2, h28, h48, h50, h51, h52, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                    · linarith only [h1, h28, h54, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                      · linarith only [h2, h28, h56, hc34, hlam, hphi, u3ehi0]
                      · linarith only [h0, h2, h48, h50, h51, h56, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h2, h50, h51, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                · linarith only [h1, h28, h50, h60, hc34, hlam, hphi, ht23, u2ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                  · linarith only [h0, h62, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                    · linarith only [h1, h2, h28, h64, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                      · linarith only [h0, h2, h28, h66, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h2, h66, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h1, h49, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · linarith only [h0, h2, h48, hc34, hlam, hphi, ht23, u2ehi1]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h72 | h72
    · linarith only [h0, h72, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
      · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
        · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
          · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
            · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
              · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
                      · linarith only [h74, h82, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                      · linarith only [h75, h82, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                    · linarith only [h72, h75, h81, hlam]
                  · linarith only [h0, h80, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h72, h74, h75, h77, h79, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
              · linarith only [h0, h74, h76, h78, hlam]
            · linarith only [h76, h77, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
            · linarith only [h72, h76, h90, hc23, hlam, hphi, u2ehi0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
              · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                      · linarith only [h74, h96, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                      · linarith only [h75, h96, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                    · linarith only [h72, h93, h95, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h0, h94, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h74, h75, h90, h93, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
              · linarith only [h74, h92, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
          · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
            · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
              · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h108 | h108
                    · linarith only [h103, h107, h108, h72, h75, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h105, h106, h108, h72, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h0, h107, h74, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi0]
                · linarith only [h104, h106, h72, hc45, hlam, hphi, ht23, ht34, u2ehi0]
              · linarith only [h0, h103, h105, h74, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h103, h104, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
            · linarith only [h103, h115, h72, hc23, hlam, hphi, u2ehi0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
              · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
                · linarith only [h115, h118, h72, h75, hc24, hlam, hphi, u2ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                    · linarith only [h120, h121, h72, h75, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h121, h72, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h103, h120, h74, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · linarith only [h103, h117, h74, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
        · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
          · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
            · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
              · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                  · linarith only [h0, h131, h74, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h0, h127, h129, h131, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h126, h128, h130, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
              · linarith only [h0, h127, h129, hc34, hlam, hphi, ht23, u2ehi0]
            · linarith only [h0, h127, h128, hc24, hlam, hphi, u2ehi0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h137 | h137
            · linarith only [h127, h137, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h139 | h139
              · linarith only [h0, h127, h139, h74, hc23, hlam, hphi, u2ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h141 | h141
                · rcases m.htr 2 3 4 (by decide) (by decide) with h142 | h142
                  · linarith only [h127, h139, h142, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h142, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h126, h137, h141, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
          · rcases m.htr 1 2 4 (by decide) (by decide) with h147 | h147
            · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
              · rcases m.htr 1 4 5 (by decide) (by decide) with h149 | h149
                · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                  · linarith only [h0, h150, h74, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h0, h150, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h147, h149, h72, hc45, hlam, hphi, ht23, ht34, u2ehi0]
              · linarith only [h0, h146, h148, hc34, hlam, hphi, ht23, u2ehi0]
            · linarith only [h0, h146, h147, hc24, hlam, hphi, u2ehi0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
            · linarith only [h146, h156, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
              · linarith only [h0, h146, h158, h74, hc23, hlam, hphi, u2ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h160 | h160
                · linarith only [h126, h156, h160, h72, hc24, hlam, hphi, u2ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                  · linarith only [h0, h162, h74, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h0, h162, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_10_12_13_25_L_I_L_R_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h13, h16, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h0, h13, h15, h16, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h15, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                              · linarith only [h14, hlam, hphi, ht23, u2ehi2, u3elo4]
                            · linarith only [h13, hlam, hphi, ht23, u2ehi2, u3elo3]
                          · linarith only [h12, h5, h7, h9, hlam, hphi, ht23, u2ehi3, u3elo0]
                        · linarith only [h10, h11, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h10, h8, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h3, h5, h9, hlam, hphi, ht23, u2ehi1, u3elo0]
                  · linarith only [h8, hlam, hphi, ht23, u2ehi1, u3elo2]
                · linarith only [h3, h7, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
              · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
              · linarith only [h29, h4, h5, hlam, hphi, ht23, u2ehi4, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                  · linarith only [h1, h29, h32, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · linarith only [h32, hlam, hphi, ht23, u2ehi1, u3elo2]
                · linarith only [h3, h31, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h4, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h37 | h37
          · linarith only [h3, h37, hc24, hlam, hphi, u2ehi4]
          · linarith only [h37, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h0, h2, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h42 | h42
    · rcases m.htr 0 1 5 (by decide) (by decide) with h43 | h43
      · rcases m.htr 0 2 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 0 2 5 (by decide) (by decide) with h45 | h45
          · rcases m.htr 0 3 4 (by decide) (by decide) with h46 | h46
            · rcases m.htr 0 3 5 (by decide) (by decide) with h47 | h47
              · rcases m.htr 0 4 5 (by decide) (by decide) with h48 | h48
                · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h57 | h57
                                  · linarith only [h0, h42, h51, h57, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h0, h42, h51, h53, h57, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h42, h51, h53, h56, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h54, h55, hlam, hphi, ht23, u2ehi3, u3elo4]
                            · linarith only [h54, hlam, hphi, ht23, u2ehi2, u3elo3]
                          · linarith only [h46, h48, h50, h53, hlam, hphi, ht23, u2ehi3, u3elo0]
                        · linarith only [h51, h52, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h49, h51, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h0, h42, h49, h50, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h49, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h44, h48, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
              · linarith only [h44, h46, h47, hlam, hphi, ht23, u2ehi3, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
              · linarith only [h45, h46, h70, hlam, hphi, ht23, u2ehi4, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h72 | h72
                · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
                  · linarith only [h42, h70, h73, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · linarith only [h0, h73, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h44, h72, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h44, h45, hc25, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h78 | h78
          · linarith only [h44, h78, hc24, hlam, hphi, u2ehi4]
          · linarith only [h78, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h42, h43, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h82 | h82
      · rcases m.htr 0 2 4 (by decide) (by decide) with h83 | h83
        · rcases m.htr 0 2 5 (by decide) (by decide) with h84 | h84
          · linarith only [h42, h82, h84, hlam, hphi, ht23, u2ehi4, u3elo1]
          · linarith only [h83, h84, hc25, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h87 | h87
          · linarith only [h83, h87, hc24, hlam, hphi, u2ehi4]
          · linarith only [h87, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h90 | h90
        · rcases m.htr 0 2 5 (by decide) (by decide) with h91 | h91
          · rcases m.htr 0 3 4 (by decide) (by decide) with h92 | h92
            · rcases m.htr 0 3 5 (by decide) (by decide) with h93 | h93
              · rcases m.htr 0 4 5 (by decide) (by decide) with h94 | h94
                · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h99 | h99
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h101 | h101
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h102 | h102
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h103 | h103
                                  · rcases h5bigk with h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h82, hlam, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h82, hc25, hlam, hphi, p104_1, u5elo1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h82, hc35, hlam, hphi, p104_1, u5elo1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h82, hc45, hlam, hphi, p104_1, u5elo1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hc05, hlam, hphi, p104_1, u5elo1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, hphi, ht23, ht34, ht45, p104_1, u2ehi4, u5elo1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h103, hc45, hlam, hphi, p104_1, u5elo1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hc45, hlam, hphi, p104_1, u5elo1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h91, hlam, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h91, hc15, hlam, hphi, p104_1, u5elo0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h103, h82, h91, hc45, hlam, hphi, p104_1, u5elo1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h82, h91, hc45, hlam, hphi, p104_1, u5elo1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h93, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h98, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h101, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hc45, hlam, hphi, p104_1, u5elo3]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h94, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h99, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h102, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h103, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                  · rcases h5bigk with h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [hlam, p130_0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h82, hlam, p130_1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h82, hc25, hlam, hphi, p130_1, u5elo1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h82, hc35, hlam, hphi, p130_1, u5elo1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h103, h82, hc34, hlam, hphi, ht45, p130_1, u5elo1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [hc05, hlam, hphi, p130_1, u5elo1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [hlam, p130_0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h102, h103, h42, h90, h92, hc34, hlam, hphi, ht23, ht45, p130_1, u2ehi4, u3elo1, u5elo1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h103, hc34, hlam, hphi, ht45, p130_1, u5elo1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h103, hc34, hlam, hphi, ht45, p130_1, u5elo1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h91, hlam, p130_1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h91, hc15, hlam, hphi, p130_1, u5elo0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [hlam, p130_0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h103, h91, hc34, hlam, hphi, ht45, p130_1, u5elo0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h103, h82, h91, hc34, hlam, hphi, ht45, p130_1, u5elo1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h93, hlam, p130_0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h98, hlam, p130_0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h101, hlam, p130_0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [hlam, p130_0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h103, hlam, p130_1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h94, hlam, p130_0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h99, hlam, p130_0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h102, hlam, p130_0]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [h102, h103, h42, h90, h92, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p130_1, u3elo1]
                                    · have p130_0 := h130c.1
                                      have p130_1 := h130c.2.1
                                      have p130_2 := h130c.2.2.1
                                      have p130_3 := h130c.2.2.2
                                      linarith only [hlam, p130_0]
                                · linarith only [h102, h42, h92, h94, hlam, hphi, ht23, u2ehi3, u3elo1]
                              · linarith only [h100, h101, hlam, hphi, ht23, u2ehi3, u3elo4]
                            · linarith only [h100, hlam, hphi, ht23, u2ehi2, u3elo3]
                          · linarith only [h42, h92, h94, h96, h99, hlam, hphi, ht23, u2ehi3, u3elo1]
                        · linarith only [h42, h93, h98, hlam]
                      · linarith only [h42, h92, h97, hlam]
                    · linarith only [h0, h90, h96, hlam]
                  · linarith only [h0, h90, h95, hc23, hlam, hphi, u2ehi3]
                · linarith only [h90, h94, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
              · linarith only [h92, h93, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
              · linarith only [h166, h91, h92, hlam, hphi, ht23, u2ehi4, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                      · linarith only [h171, h92, hc03, hlam, hphi, u3elo1]
                      · linarith only [h171, h42, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h170, h90, hlam]
                  · linarith only [h0, h169, h90, hc23, hlam, hphi, u2ehi3]
                · linarith only [h168, h90, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h90, h91, hc25, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h178 | h178
          · linarith only [h178, h90, hc24, hlam, hphi, u2ehi4]
          · linarith only [h178, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_10_12_13_25_L_R_L_0_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h0emin := hb0.2.2
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                                  · linarith only [h13, h16, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h0, h15, h16, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                                  · linarith only [h15, h19, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                  · rcases h0emin with h21 | h21 | h21 | h21 | h21
                                    · rcases h5bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [hlam, p22_0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22_1, u3elo0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22_1, u3elo0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22_1, u3elo0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h13, h15, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p22_1, u3elo0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h2, hlam, p22_0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [hlam, p22_0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p22_1]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h2, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22_1, u3elo0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h13, h15, h2, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p22_1, u3elo0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h5, hlam, p22_1]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h10, hlam, p22_1]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [hlam, p22_0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p22_1, u2elo4]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h15, hlam, p22_1]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h7, hlam, p22_0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h11, hlam, p22_0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h14, hlam, p22_0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [hlam, p22_0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h19, hlam, p22_1]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h8, hlam, p22_0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h12, hlam, p22_0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22_1, u3elo0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22_1, u3elo0]
                                      · have p22_0 := h22c.1
                                        have p22_1 := h22c.2.1
                                        have p22_2 := h22c.2.2.1
                                        have p22_3 := h22c.2.2.2
                                        linarith only [hlam, p22_0]
                                    · linarith only [h21, hlam, ht01, ht12, u2elo0]
                                    · linarith only [h21, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h21, h6, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h21, h6, h8, hlam, ht01, ht12, ht23, u3elo0]
                              · linarith only [h14, h7, hc23, hlam, hphi, u3elo0]
                            · linarith only [h13, h6, hc23, hlam, hphi, u3elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                                · linarith only [h12, h4, h56, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                                  · linarith only [h12, h54, h58, h9, hlam]
                                  · rcases h0emin with h60 | h60 | h60 | h60 | h60
                                    · rcases h5bigk with h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [hlam, p61_0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p61_1, u3elo0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p61_1, u3elo0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h58, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p61_1, u3elo0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h12, h54, h6, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p61_1, u3elo0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h2, hlam, p61_0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [hlam, p61_0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p61_1]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h2, h58, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p61_1, u3elo0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h12, hlam, p61_1]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h5, hlam, p61_1]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h10, hlam, p61_1]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [hlam, p61_0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h58, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p61_1, u2elo4]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h56, hlam, p61_1]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h7, hlam, p61_0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h11, hlam, p61_0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h55, hlam, p61_0]
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
                                        linarith only [h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p61_1, u3elo0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p61_1, u3elo0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [h58, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p61_1, u3elo0]
                                      · have p61_0 := h61c.1
                                        have p61_1 := h61c.2.1
                                        have p61_2 := h61c.2.2.1
                                        have p61_3 := h61c.2.2.2
                                        linarith only [hlam, p61_0]
                                    · linarith only [h60, hlam, ht01, ht12, u2elo0]
                                    · linarith only [h60, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h6, h60, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h6, h60, h8, hlam, ht01, ht12, ht23, u3elo0]
                              · linarith only [h55, h7, hc23, hlam, hphi, u3elo0]
                            · linarith only [h54, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h11, h7, hc13, hlam, hphi, u3elo0]
                      · linarith only [h10, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h99 | h99
                          · linarith only [h8, h99, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                                · linarith only [h103, h8, h96, hc12, hlam, hphi, ht01, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                                  · linarith only [h105, h8, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo3]
                                  · rcases h0emin with h107 | h107 | h107 | h107 | h107
                                    · rcases h5bigk with h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [hlam, p108_0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p108_1, u3elo0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h103, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u3elo0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h105, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u3elo0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h8, hlam, p108_1]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h2, hlam, p108_0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [hlam, p108_0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h103, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p108_1]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h105, h2, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u3elo0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h99, hlam, p108_1]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h5, hlam, p108_1]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h97, hlam, p108_1]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [hlam, p108_0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h105, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p108_1, u2elo4]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h103, hlam, p108_1]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h7, hlam, p108_0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h98, hlam, p108_0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h102, hlam, p108_0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [hlam, p108_0]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h105, hlam, p108_1]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p108_1, u0ehi4]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h105, h98, hc34, hc45, hlam, hphi, p108_1]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h102, h105, hc34, hc45, hlam, hphi, p108_1]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [h105, hc34, hc45, hlam, hphi, p108_1]
                                      · have p108_0 := h108c.1
                                        have p108_1 := h108c.2.1
                                        have p108_2 := h108c.2.2.1
                                        have p108_3 := h108c.2.2.2
                                        linarith only [hlam, p108_0]
                                    · linarith only [h107, hlam, ht01, ht12, u2elo0]
                                    · linarith only [h107, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h107, h4, hlam, ht01, ht12, u2elo0]
                                    · linarith only [h107, h5, hlam, ht01, ht12, u2elo0]
                              · linarith only [h102, h7, hc23, hlam, hphi, u3elo0]
                            · linarith only [h101, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h7, h98, hc13, hlam, hphi, u3elo0]
                      · linarith only [h5, h97, hc12, hlam, hphi, u2elo0]
                    · linarith only [h4, h96, hc12, hlam, hphi, u2elo0]
                · linarith only [h7, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
              · linarith only [h6, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
            · linarith only [h5, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
          · linarith only [h3, h4, hlam, hphi, ht01, ht12, u0ehi2, u2elo3]
        · linarith only [h3, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h148 | h148
        · rcases m.htr 0 2 4 (by decide) (by decide) with h149 | h149
          · rcases m.htr 0 2 5 (by decide) (by decide) with h150 | h150
            · linarith only [h0, h150, h2, hlam]
            · linarith only [h150, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
          · linarith only [h148, h149, hlam, hphi, ht01, ht12, u0ehi2, u2elo3]
        · linarith only [h148, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
    · linarith only [h0, h1, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo1]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_10_12_13_25_L_R_L_I_L_R_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
              · linarith only [h3, h4, h5, h7, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h0, h3, h4, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
            · linarith only [h10, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                · linarith only [h0, h1, h13, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h12, h13, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                · linarith only [h12, h16, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h18, h20, h4, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h12, h20, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
          · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
            · linarith only [h0, h24, h3, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
              · linarith only [h1, h26, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                · linarith only [h0, h23, h26, h28, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h0, h23, h26, h28, h3, hc35, hlam, hphi, u3ehi2]
          · linarith only [h2, h23, h3, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h32 | h32
        · linarith only [h2, h32, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
          · linarith only [h2, h34, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
            · linarith only [h0, h2, h32, h36, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
              · linarith only [h1, h2, h38, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h1, h2, h38, hc34, hlam, hphi, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h41 | h41
      · rcases m.htr 0 2 5 (by decide) (by decide) with h42 | h42
        · linarith only [h1, h42, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
          · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
            · linarith only [h0, h42, h45, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
              · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
                  · linarith only [h0, h42, h44, h48, h49, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h42, h44, h47, h49, hc45, hlam, hphi, ht34, u3ehi3]
                · linarith only [h0, h1, h44, h47, h48, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h47, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
          · linarith only [h1, h41, h44, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h55 | h55
        · linarith only [h1, h55, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
          · linarith only [h41, h57, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
            · linarith only [h0, h55, h59, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
              · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                    · linarith only [h61, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases h2bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h55, h63, hc12, hc24, hlam, hphi, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h1, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h41, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h55, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h61, h63, h64, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p66_1, u3ehi3]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h57, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h59, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hc23, hlam, hphi, ht01, ht12, p66_1, u0ehi1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        rcases p66_3 (m.d 0 2) (by simp) with h78 | h78
                        · linarith only [h1, h78, hlam]
                        · linarith only [h0, h78, hlam]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h63, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u3ehi3]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p66_1, u5ehi2]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hc24, hlam, hphi, ht01, ht12, p66_1, u0ehi1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        rcases p66_3 (m.d 0 2) (by simp) with h85 | h85
                        · linarith only [h41, h85, hlam]
                        · linarith only [h0, h85, hlam]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h61, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h55, h61, hc23, hlam, hphi, ht01, ht12, p66_1, u0ehi1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hc25, hlam, hphi, ht01, ht12, p66_1, u0ehi1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        rcases p66_3 (m.d 0 2) (by simp) with h92 | h92
                        · linarith only [h55, h92, hlam]
                        · linarith only [h0, h92, hlam]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h62, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h63, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                  · linarith only [h41, h63, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                · linarith only [h1, h62, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
              · linarith only [h1, h61, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h101 | h101
    · rcases m.htr 0 2 4 (by decide) (by decide) with h102 | h102
      · rcases m.htr 0 2 5 (by decide) (by decide) with h103 | h103
        · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
          · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
            · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
              · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                · linarith only [h101, h107, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h106, h107, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                · linarith only [h106, h110, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
                  · linarith only [h0, h102, h112, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h114 | h114
                    · linarith only [h106, h112, h114, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h106, h114, hc45, hlam, hphi, ht34, u3ehi2]
            · linarith only [h0, h105, hc25, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h103, h104, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
          · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
            · linarith only [h103, h120, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h120, hc25, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h102, h119, hc02, hlam, hphi, u0ehi0]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h124 | h124
        · linarith only [h102, h124, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
          · linarith only [h102, h126, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h126, hc24, hlam, hphi, ht01, ht12, u0ehi0]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h129 | h129
      · rcases m.htr 0 2 5 (by decide) (by decide) with h130 | h130
        · linarith only [h101, h130, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
          · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
            · linarith only [h130, h133, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h133, hc25, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h101, h129, h132, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h137 | h137
        · linarith only [h101, h137, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
          · linarith only [h129, h139, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h139, hc24, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
