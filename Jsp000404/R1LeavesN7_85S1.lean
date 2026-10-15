import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_13_25_L_0_L_0_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h2, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
              · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, h2, h8, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
                    · linarith only [h1, h10, h13, h2, h5, h8, hc02, hlam, hphi, ht23, u3elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h1, h16, h2, h8, hlam]
                        · linarith only [h1, h10, h16, h2, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h10, h12, h15, h7, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · linarith only [h0, h12, h2, h4, h8, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
              · linarith only [h21, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h2, h21, h23, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h1, h2, h21, h23, h26, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                      · linarith only [h1, h2, h21, h28, h7, hc03, hlam, hphi, u3elo4]
                      · linarith only [h23, h25, h28, hlam]
                  · linarith only [h0, h2, h21, h25, h4, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h32 | h32
          · linarith only [h0, h32, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
            · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
              · linarith only [h35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                · linarith only [h0, h34, h35, h37, h4, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                  · linarith only [h0, h39, h4, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
                    · linarith only [h1, h2, h32, h37, h41, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                        · linarith only [h1, h2, h35, h44, hlam]
                        · linarith only [h1, h2, h43, h44, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h34, h43, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h48 | h48
              · linarith only [h34, h48, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
                · linarith only [h0, h2, h48, h50, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                  · linarith only [h0, h4, h52, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h54 | h54
                    · linarith only [h1, h2, h48, h50, h54, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                      · linarith only [h1, h2, h34, h48, h56, hc03, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                        · linarith only [h1, h2, h48, h58, hlam]
                        · linarith only [h1, h2, h50, h58, hc12, hlam, hphi, ht23, u3elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h62 | h62
    · rcases m.htr 0 1 5 (by decide) (by decide) with h63 | h63
      · linarith only [h63, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h65 | h65
        · rcases m.htr 0 2 5 (by decide) (by decide) with h66 | h66
          · linarith only [h66, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h68 | h68
            · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
              · linarith only [h69, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h74 | h74
                      · linarith only [h0, h62, h66, h73, h74, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h68, h69, h71, h74, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                      · linarith only [h0, h62, h73, h77, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h68, h69, h71, h77, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h62, h65, h71, h72, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h71, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h82 | h82
              · linarith only [h82, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                      · linarith only [h62, h68, h87, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                        · linarith only [h62, h82, h89, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                        · linarith only [h0, h62, h66, h84, h86, h89, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                      · linarith only [h62, h68, h92, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                        · linarith only [h62, h94, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h0, h62, h84, h86, h94, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h62, h65, h66, h82, h84, h85, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h84, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h99 | h99
          · linarith only [h99, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h101 | h101
            · linarith only [h0, h101, h62, h65, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h103 | h103
              · linarith only [h103, h62, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                      · linarith only [h0, h101, h108, h62, h65, hlam]
                      · linarith only [h0, h106, h108, h62, h65, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h105, h106, h107, h62, h65, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
                    · linarith only [h106, h112, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                      · linarith only [h101, h114, h62, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h105, h106, h114, h62, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h105, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h118 | h118
      · linarith only [h118, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h120 | h120
        · rcases m.htr 0 2 5 (by decide) (by decide) with h121 | h121
          · linarith only [h121, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
            · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
              · linarith only [h124, h62, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
                · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h130 | h130
                        · linarith only [h124, h130, hc03, hlam, hphi, u3elo1]
                        · linarith only [h130, h62, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h123, h129, h62, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                        · linarith only [h124, h126, h128, h135, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · linarith only [h135, h62, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h123, h134, h62, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h120, h126, h127, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h126, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h141 | h141
              · linarith only [h120, h123, h141, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
                · rcases m.htr 1 2 4 (by decide) (by decide) with h144 | h144
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h145 | h145
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                      · linarith only [h123, h146, hc03, hlam, hphi, u3elo1]
                      · linarith only [h146, h62, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                      · linarith only [h123, h149, h62, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h149, h62, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h120, h143, h144, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h143, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h154 | h154
          · linarith only [h154, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h156 | h156
            · rcases m.htr 0 3 5 (by decide) (by decide) with h157 | h157
              · linarith only [h157, h62, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h159 | h159
                · rcases m.htr 1 2 4 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
                        · linarith only [h157, h163, hc03, hlam, hphi, u3elo1]
                        · linarith only [h163, h62, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h162, h62, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h120, h160, h161, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
                    · linarith only [h160, h168, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                      · linarith only [h159, h160, h170, hlam]
                      · linarith only [h156, h170, hc13, hlam, hphi, u3elo0]
                · linarith only [h0, h159, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h174 | h174
              · linarith only [h174, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
                · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                      · linarith only [h156, h179, hc03, hlam, hphi, u3elo1]
                      · linarith only [h179, h62, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h120, h177, h178, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                    · linarith only [h177, h183, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                      · linarith only [h156, h185, h62, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h185, h62, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h176, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_11_12_14_25_L_0_L_0_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                      · linarith only [h10, h9, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h3, h9, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h15, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                      · linarith only [h15, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h14, h3, hc12, hlam, hphi, u2elo0]
                · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h20 | h20
                · linarith only [h20, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h24, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                      · linarith only [h24, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h23, h3, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                      · linarith only [h0, h29, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                      · linarith only [h29, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h28, h3, hc12, hlam, hphi, u2elo0]
            · linarith only [h3, h5, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h3, h4, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h35 | h35
          · rcases m.htr 0 2 5 (by decide) (by decide) with h36 | h36
            · linarith only [h3, h36, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
            · linarith only [h35, h36, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h39 | h39
            · linarith only [h35, h39, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h41 | h41
              · rcases m.htr 0 3 5 (by decide) (by decide) with h42 | h42
                · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                    · linarith only [h0, h35, h39, h43, h44, hc23, hlam, hphi, ht34, u4elo2, u5ehi9, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                      · linarith only [h0, h39, h46, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                          · linarith only [h1, h48, h49, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                          · linarith only [h35, h43, h49, hc14, hlam, hphi, u4elo2]
                        · linarith only [h3, h41, h44, h48, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                    · linarith only [h3, h42, h53, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                      · linarith only [h0, h35, h43, h55, hlam, hphi, u5ehi7, u5elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                          · linarith only [h35, h43, h58, hc02, hlam, hphi, ht23, ht34, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                                · linarith only [h58, h62, hc14, hlam, hphi, u4elo2]
                                · linarith only [h0, h35, h62, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h0, h3, h61, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                            · linarith only [h3, h42, h57, h60, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi8]
                        · linarith only [h41, h43, h57, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h41, h42, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
                · linarith only [h41, h69, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                    · linarith only [h0, h3, h35, h69, h71, h72, hc23, hlam, hphi, ht34, u4elo2, u5ehi9, u5elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                      · linarith only [h0, h3, h39, h69, h74, hlam, hphi, u5ehi5, u5elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                        · linarith only [h1, h35, h69, h71, h76, hc34, hlam, hphi, u4elo2, u5ehi9, u5elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                            · linarith only [h41, h71, h79, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                            · linarith only [h0, h3, h79, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h71, h78, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
                    · linarith only [h0, h3, h83, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                      · linarith only [h0, h39, h85, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                        · linarith only [h1, h41, h71, h87, hc34, hlam, hphi, ht45, u5elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                          · linarith only [h0, h3, h41, h71, h89, hc12, hlam, hphi, ht23, ht34, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                            · linarith only [h0, h3, h41, h91, hc12, hlam, hphi, u2elo2]
                            · linarith only [h0, h3, h91, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h95 | h95
      · linarith only [h1, h95, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi6]
      · linarith only [h0, h95, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h98 | h98
    · rcases m.htr 0 1 5 (by decide) (by decide) with h99 | h99
      · linarith only [h0, h99, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
      · linarith only [h98, h99, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h102 | h102
      · linarith only [h102, h98, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi6]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h104 | h104
        · rcases m.htr 0 2 4 (by decide) (by decide) with h105 | h105
          · rcases m.htr 0 2 5 (by decide) (by decide) with h106 | h106
            · rcases m.htr 0 3 4 (by decide) (by decide) with h107 | h107
              · rcases m.htr 0 3 5 (by decide) (by decide) with h108 | h108
                · rcases m.htr 0 4 5 (by decide) (by decide) with h109 | h109
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                              · linarith only [h0, h104, h115, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                              · linarith only [h108, h110, h114, h115, h98, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                              · linarith only [h114, h118, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
                                · linarith only [h0, h105, h120, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
                                · linarith only [h109, h120, hc24, hlam, hphi, u4elo0]
                          · linarith only [h109, h113, hc14, hlam, hphi, u4elo0]
                        · linarith only [h107, h112, h98, hlam]
                      · linarith only [h107, h110, h111, h98, hc34, hlam, hphi, ht45, u5elo2]
                    · linarith only [h0, h104, h107, h109, h110, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                          · linarith only [h109, h130, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h133 | h133
                              · linarith only [h0, h104, h133, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                              · linarith only [h108, h132, h133, h98, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · linarith only [h107, h109, h132, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h107, h109, h129, hc13, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h106, h128, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                    · linarith only [h0, h104, h108, h127, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
                · linarith only [h107, h108, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h141 | h141
                · linarith only [h107, h141, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h143 | h143
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h145 | h145
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                        · linarith only [h107, h146, h98, hc01, hlam, hphi, u1elo2]
                        · linarith only [h146, h98, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h105, h143, h145, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi9]
                    · linarith only [h0, h105, h143, h144, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h153 | h153
                        · linarith only [h107, h151, h153, h98, hc01, hlam, hphi, u1elo1]
                        · linarith only [h153, h98, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h106, h152, hc12, hlam, hphi, u2elo0]
                    · linarith only [h0, h104, h107, h143, h151, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h104, h106, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h104, h105, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h160 | h160
          · rcases m.htr 0 2 5 (by decide) (by decide) with h161 | h161
            · linarith only [h104, h161, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
            · linarith only [h160, h161, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h164 | h164
            · linarith only [h160, h164, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h166 | h166
              · rcases m.htr 0 3 5 (by decide) (by decide) with h167 | h167
                · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                    · linarith only [h104, h169, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h169, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h172 | h172
                    · linarith only [h0, h104, h172, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h172, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h166, h167, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h176 | h176
                · linarith only [h166, h176, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                    · linarith only [h0, h104, h179, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h179, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h182 | h182
                    · linarith only [h0, h104, h182, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h182, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_11_12_14_25_L_0_L_I_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h6 | h6
        · linarith only [h2, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h8 | h8
          · rcases m.htr 0 2 4 (by decide) (by decide) with h9 | h9
            · linarith only [h0, h2, h9, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13 | h13
                · linarith only [h13, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, h2, h9, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
                    · linarith only [h1, h17, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h1, h19, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h13, h21, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                        · linarith only [h0, h2, h21, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h24 | h24
            · linarith only [h1, h2, h24, h8, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h26 | h26
              · linarith only [h1, h2, h26, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
                · linarith only [h2, h28, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
                  · linarith only [h0, h2, h24, h30, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                    · linarith only [h1, h2, h32, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                      · linarith only [h1, h2, h34, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                        · linarith only [h36, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                        · linarith only [h0, h2, h36, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h39 | h39
      · linarith only [h1, h39, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h41 | h41
        · linarith only [h1, h41, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h43 | h43
          · linarith only [h0, h1, h43, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h45 | h45
            · linarith only [h0, h1, h45, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h47 | h47
              · linarith only [h0, h1, h47, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h49 | h49
                · linarith only [h39, h49, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                  · linarith only [h0, h1, h45, h51, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
                      · linarith only [h54, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · linarith only [h0, h39, h53, h54, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h53, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h58 | h58
    · rcases m.htr 0 1 4 (by decide) (by decide) with h59 | h59
      · linarith only [h0, h59, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h61 | h61
        · linarith only [h0, h61, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h63 | h63
          · rcases m.htr 0 2 4 (by decide) (by decide) with h64 | h64
            · rcases m.htr 0 2 5 (by decide) (by decide) with h65 | h65
              · linarith only [h0, h65, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
                · linarith only [h59, h67, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h70 | h70
                    · linarith only [h58, h59, h69, h70, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h72 | h72
                      · linarith only [h58, h59, h69, h72, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
                        · linarith only [h67, h69, h74, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                        · linarith only [h58, h59, h74, hc13, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h58, h61, h64, h65, h69, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h78 | h78
              · linarith only [h64, h78, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h80 | h80
                · linarith only [h59, h80, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                  · linarith only [h63, h64, h82, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                    · linarith only [h0, h58, h84, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                      · linarith only [h0, h58, h82, h86, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h88 | h88
                        · linarith only [h80, h88, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                        · linarith only [h58, h59, h88, hc13, hc45, hlam, hphi, ht34]
          · linarith only [h0, h58, h63, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h92 | h92
      · linarith only [h58, h92, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h94 | h94
        · linarith only [h0, h94, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h96 | h96
          · rcases m.htr 0 2 4 (by decide) (by decide) with h97 | h97
            · rcases m.htr 0 2 5 (by decide) (by decide) with h98 | h98
              · linarith only [h0, h98, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
                · linarith only [h100, h92, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
                      · linarith only [h104, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                        · linarith only [h100, h103, h104, h106, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                          · linarith only [h108, h94, h96, h98, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi3]
                          · linarith only [h103, h104, h108, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h111 | h111
                      · linarith only [h111, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                        · linarith only [h102, h113, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                          · linarith only [h115, h94, h96, h98, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                            · linarith only [h103, h113, h117, h58, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h117, h97, h98, hc45, hlam, hphi, u4ehi2]
                  · linarith only [h102, h97, h98, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h121 | h121
              · linarith only [h0, h121, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h123 | h123
                · linarith only [h123, h92, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                  · linarith only [h0, h125, h97, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                      · linarith only [h128, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                        · linarith only [h127, h128, h130, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                          · linarith only [h121, h132, h96, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h127, h128, h132, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                      · linarith only [h135, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                        · linarith only [h123, h137, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h139 | h139
                          · linarith only [h137, h139, h92, h96, h97, hc45, hlam, hphi, u4ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                            · linarith only [h137, h139, h141, h92, h96, h97, hc23, hc34, hlam, hphi]
                            · linarith only [h141, h96, h97, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h144 | h144
            · rcases m.htr 0 2 5 (by decide) (by decide) with h145 | h145
              · linarith only [h145, h58, h96, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h147 | h147
                · linarith only [h144, h147, h58, h96, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
                      · linarith only [h151, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
                        · linarith only [h147, h150, h151, h153, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                            · linarith only [h153, h156, h92, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h144, h145, h156, hc45, hlam, hphi, u4ehi2]
                          · linarith only [h144, h155, h96, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                      · linarith only [h160, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h162 | h162
                        · linarith only [h149, h162, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                        · linarith only [h144, h150, h162, h58, h96, hc45, hlam, hphi, u4ehi2]
                  · linarith only [h144, h149, h96, hc12, hc23, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h166 | h166
              · linarith only [h166, h96, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                · linarith only [h168, h92, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
                  · linarith only [h0, h144, h170, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                      · linarith only [h173, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                        · linarith only [h168, h172, h173, h175, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                            · linarith only [h0, h170, h175, h177, h178, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h170, h178, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h172, h173, h177, h96, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h182 | h182
                      · linarith only [h182, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                        · linarith only [h184, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h186 | h186
                          · linarith only [h172, h186, h58, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h188 | h188
                            · linarith only [h184, h188, h92, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h0, h170, h188, hc01, hc45, hlam, hphi, ht12, ht23, ht34]

theorem r1l7_11_12_14_25_L_I_L_R_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · linarith only [h2, h4, hc25, hlam, hphi, u2ehi2]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
        · linarith only [h2, h8, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
          · linarith only [h10, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
              · linarith only [h1, h13, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h13, h17, h8, hc24, hlam, hphi, u2ehi1]
                    · linarith only [h17, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · linarith only [h16, h2, hc35, hlam, hphi, ht23, u2ehi1]
                · linarith only [h12, h15, h2, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
              · linarith only [h1, h22, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                · linarith only [h12, h2, h24, hc23, hlam, hphi, u2ehi1]
                · linarith only [h2, h24, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
      · linarith only [h0, h1, h27, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
        · linarith only [h0, h1, h29, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · linarith only [h0, h1, h29, hc24, hlam, hphi, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h32 | h32
    · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
      · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
        · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
          · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
            · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
              · linarith only [h32, h37, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                  · linarith only [h33, h40, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                    · linarith only [h34, h37, h42, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h37, h39, h40, h44, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h39, h40, h44, hc45, hlam, hphi, u4ehi3]
                · linarith only [h0, h32, h36, h39, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h48 | h48
              · linarith only [h0, h32, h48, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                · linarith only [h0, h32, h33, h36, h50, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                  · linarith only [h33, h52, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                    · linarith only [h33, h36, h48, h54, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                      · linarith only [h33, h36, h48, h56, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h33, h36, h56, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h32, h35, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h0, h32, h34, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h0, h32, h33, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
      · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
        · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
          · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
            · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
              · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                  · linarith only [h62, h68, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                    · linarith only [h67, h68, h70, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                      · linarith only [h67, h68, h70, h72, hc35, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h65, h66, h67, h68, h72, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                  · linarith only [h62, h65, h67, h75, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
                    · linarith only [h63, h77, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                      · linarith only [h62, h65, h67, h77, h79, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h67, h79, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                  · linarith only [h62, h83, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                    · linarith only [h32, h66, h85, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                      · linarith only [h32, h66, h87, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h82, h83, h87, hc45, hlam, hphi, u4ehi3]
                · linarith only [h65, h66, h82, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
              · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                · linarith only [h65, h91, h92, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                  · linarith only [h62, h65, h94, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                    · linarith only [h63, h96, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h65, h91, h96, hc34, hlam, hphi, ht23, u2ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                · linarith only [h62, h65, h91, h99, hc45, hlam, hphi, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h101 | h101
                  · linarith only [h101, h62, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                    · linarith only [h103, h63, h91, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                      · linarith only [h105, h62, h65, h91, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h105, h62, h65, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h62, h64, hc25, hlam, hphi, u2ehi2]
        · linarith only [h62, h63, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
        · linarith only [h110, h62, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
          · linarith only [h112, h62, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
            · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
              · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                · rcases m.htr 2 3 5 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                      · linarith only [h114, h119, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases h1bigk with h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [hlam, p121_0]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h0, hlam, p121_0]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h0, h112, h116, h118, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p121_1]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h32, hlam, p121_0]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h0, h112, hlam, p121_1]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h112, h116, h118, hc01, hc23, hlam, hphi, ht12, p121_1]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [hlam, p121_0]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h62, hlam, p121_1]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h110, hlam, p121_1]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h112, hlam, p121_1]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          rcases p121_3 (m.d 0 1) (by simp) with h132 | h132
                          · linarith only [h132, hlam, p121_0]
                          · rcases p121_3 (m.d 1 2) (by simp) with h134 | h134
                            · linarith only [h134, h62, hlam]
                            · linarith only [h0, h134, hlam]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h0, hc01, hc13, hlam, hphi, p121_1]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [hlam, p121_0]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h115, h119, h62, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p121_1, u4ehi3]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h115, h119, h62, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p121_1, u4ehi3]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          rcases p121_3 (m.d 0 1) (by simp) with h141 | h141
                          · linarith only [h141, hlam, p121_0]
                          · rcases p121_3 (m.d 1 2) (by simp) with h143 | h143
                            · linarith only [h110, h143, hlam]
                            · linarith only [h0, h143, hlam]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p121_1]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h114, hlam, p121_1]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [hlam, p121_0]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h110, h115, h116, h119, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p121_1, u4ehi3]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          rcases p121_3 (m.d 0 1) (by simp) with h150 | h150
                          · linarith only [h150, hlam, p121_0]
                          · rcases p121_3 (m.d 1 2) (by simp) with h152 | h152
                            · linarith only [h112, h152, hlam]
                            · linarith only [h0, h152, hlam]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p121_1]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h0, h112, h116, h118, h62, hc23, hlam, hphi, p121_1, u2ehi0]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [h115, hlam, p121_0]
                        · have p121_0 := h121c.1
                          have p121_1 := h121c.2.1
                          have p121_2 := h121c.2.2.1
                          have p121_3 := h121c.2.2.2
                          linarith only [hlam, p121_0]
                    · linarith only [h0, h110, h118, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h0, h117, h62, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h114, h115, h116, h62, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                · rcases m.htr 2 3 5 (by decide) (by decide) with h163 | h163
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                    · linarith only [h115, h162, h164, h32, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h110, h164, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h163, h62, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h114, h162, h62, hc01, hc13, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h169 | h169
              · rcases m.htr 2 3 4 (by decide) (by decide) with h170 | h170
                · linarith only [h0, h114, h170, h62, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h170, h62, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                · linarith only [h0, h114, h173, h62, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h173, h62, hc01, hc34, hlam, hphi, ht12, ht23]

theorem r1l7_11_12_14_25_L_I_L_R_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
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
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h10, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h8, h9, hlam, hphi, ht45, u4ehi2, u5elo3]
                  · linarith only [h0, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h6, h7, hlam, hphi, ht45, u4ehi1, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                  · linarith only [h16, h17, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                      · rcases h1bigk with h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h19, h20, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p21_1, u4ehi4]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h19, h20, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p21_1, u4ehi4]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h19, h20, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p21_1, u4ehi4]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          rcases p21_3 (m.d 0 1) (by simp) with h26 | h26
                          · rcases p21_3 (m.d 1 2) (by simp) with h27 | h27
                            · rcases p21_3 (m.d 1 3) (by simp) with h28 | h28
                              · linarith only [h0, h28, hlam]
                              · linarith only [h16, h28, hlam]
                            · linarith only [h27, h5, hlam]
                          · linarith only [h26, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h19, h20, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p21_1, u4ehi4]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h19, h20, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p21_1, u4ehi4]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h19, h20, h4, h6, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p21_1, u4ehi4]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          rcases p21_3 (m.d 0 1) (by simp) with h37 | h37
                          · rcases p21_3 (m.d 1 2) (by simp) with h38 | h38
                            · rcases p21_3 (m.d 1 3) (by simp) with h39 | h39
                              · linarith only [h39, h4, hlam]
                              · linarith only [h16, h39, hlam]
                            · linarith only [h38, h5, hlam]
                          · linarith only [h2, h37, hlam]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h4, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h6, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h5, h6, hc34, hlam, hphi, ht23, p21_1, u2ehi4]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h1, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h1, h19, h20, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p21_1, u2ehi1, u4ehi4]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h19, h20, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p21_1, u4ehi4]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h1, h19, h20, h4, h5, h6, hc01, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p21_1, u2ehi4, u4ehi4]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h2, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h5, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h16, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, hphi, ht45, p21_1, u4ehi1, u5elo1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                      · linarith only [h19, h20, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                    · linarith only [h16, h19, h6, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h16, h4, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
            · linarith only [h4, h5, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
            · linarith only [h4, h63, hc23, hlam, hphi, u2ehi4]
            · linarith only [h63, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h1, h2, hlam, hphi, ht45, u4ehi0, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h68 | h68
      · rcases m.htr 0 2 5 (by decide) (by decide) with h69 | h69
        · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
          · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
              · linarith only [h0, h1, h72, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h1, h68, h71, h72, hc34, hlam, hphi, ht23, u2ehi4]
            · linarith only [h71, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
            · linarith only [h70, h76, hc23, hlam, hphi, u2ehi4]
            · linarith only [h76, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
        · linarith only [h69, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h0, h68, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h81 | h81
    · rcases m.htr 0 1 5 (by decide) (by decide) with h82 | h82
      · rcases m.htr 0 2 5 (by decide) (by decide) with h83 | h83
        · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
          · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
            · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
              · rcases m.htr 1 3 5 (by decide) (by decide) with h87 | h87
                · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h90 | h90
                      · linarith only [h0, h81, h84, h86, h90, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h90, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h89, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · linarith only [h0, h81, h84, h86, h88, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h81, h87, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h0, h82, h85, h86, hc34, hlam, hphi, ht23, u2ehi4]
            · linarith only [h0, h82, h83, h84, h85, hc02, hlam, hphi, ht0b, ht5b, u5ehi6]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
            · linarith only [h84, h98, hc23, hlam, hphi, u2ehi4]
            · linarith only [h98, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
        · linarith only [h83, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h81, h82, hlam, hphi, ht45, u4ehi1, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h103 | h103
      · rcases m.htr 0 2 5 (by decide) (by decide) with h104 | h104
        · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
          · rcases m.htr 1 2 5 (by decide) (by decide) with h106 | h106
            · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
              · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
                · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h111 | h111
                      · linarith only [h105, h109, h111, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                      · linarith only [h111, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h110, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                    · linarith only [h107, h109, h115, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · linarith only [h115, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                · linarith only [h107, h108, hlam, hphi, ht45, u4ehi3, u5elo3]
              · linarith only [h0, h103, h106, h107, hc34, hlam, hphi, ht23, u2ehi4]
            · linarith only [h106, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
            · linarith only [h105, h121, hc23, hlam, hphi, u2ehi4]
            · linarith only [h121, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
        · linarith only [h104, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h125 | h125
        · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
          · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
            · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
              · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h132 | h132
                      · linarith only [h126, h130, h132, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h132, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h131, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                    · linarith only [h128, h130, h136, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · linarith only [h136, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                · linarith only [h128, h129, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
                · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                  · linarith only [h128, h140, h141, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h143 | h143
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
                      · rcases h1bigk with h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h103, h126, h128, h143, h144, hc34, hlam, hphi, ht23, ht45, p145_1, u2ehi1, u4ehi4, u5elo1]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h0, hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h81, hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h103, hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          rcases p145_3 (m.d 0 1) (by simp) with h151 | h151
                          · linarith only [h151, hlam, p145_0]
                          · rcases p145_3 (m.d 1 2) (by simp) with h153 | h153
                            · rcases p145_3 (m.d 1 3) (by simp) with h154 | h154
                              · linarith only [h126, h154, hlam]
                              · linarith only [h0, h154, hlam]
                            · linarith only [h153, hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h126, h143, h144, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p145_1, u4ehi4]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h126, h128, h143, h144, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p145_1, u4ehi4]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h103, hc01, hc12, hlam, hphi, p145_1]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h128, hc01, hc34, hlam, hphi, ht12, ht23, p145_1]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h126, hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h128, hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h103, h125, h128, hc34, hlam, hphi, ht23, p145_1, u2ehi4]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          rcases p145_3 (m.d 0 1) (by simp) with h167 | h167
                          · linarith only [h167, hlam, p145_0]
                          · rcases p145_3 (m.d 1 2) (by simp) with h169 | h169
                            · rcases p145_3 (m.d 1 3) (by simp) with h170 | h170
                              · linarith only [h128, h170, hlam]
                              · linarith only [h0, h170, hlam]
                            · linarith only [h0, h128, h169, hc34, hlam, hphi, ht23, u2ehi1]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h126, h143, h144, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p145_1, u4ehi4]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h126, h128, h143, h144, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p145_1, u4ehi4]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h103, h128, hc01, hc34, hlam, hphi, ht12, ht23, p145_1]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p145_1, u5elo1]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h127, hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [h140, hlam, p145_0]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [hlam, hphi, ht45, p145_1, u4ehi1, u5elo1]
                        · have p145_0 := h145c.1
                          have p145_1 := h145c.2.1
                          have p145_2 := h145c.2.2.1
                          have p145_3 := h145c.2.2.2
                          linarith only [hlam, p145_0]
                      · linarith only [h126, h128, h143, h144, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                    · linarith only [h128, h140, h143, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h0, h140, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h125, h126, h127, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h187 | h187
            · linarith only [h126, h187, hc23, hlam, hphi, u2ehi4]
            · linarith only [h187, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
        · linarith only [h125, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_11_12_14_25_L_R_L_0_L_I_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h5elo := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h12, h15, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · linarith only [h0, h12, h14, h15, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                                · linarith only [h14, h18, h3, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                · rcases h4bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h3, h5, hlam, hphi, ht12, p20_1, u1ehi3, u2elo0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    rcases p20_3 (m.d 0 4) (by simp) with h23 | h23
                                    · rcases p20_3 (m.d 1 4) (by simp) with h24 | h24
                                      · linarith only [h1, h24, hlam]
                                      · linarith only [h24, h8, hlam]
                                    · linarith only [h23, h4, hlam]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    rcases p20_3 (m.d 0 4) (by simp) with h28 | h28
                                    · rcases p20_3 (m.d 1 4) (by simp) with h29 | h29
                                      · linarith only [h1, h29, hlam]
                                      · linarith only [h29, h9, hlam]
                                    · linarith only [h28, h5, hlam]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h12, h14, h3, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h1, hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    rcases p20_3 (m.d 0 4) (by simp) with h36 | h36
                                    · rcases p20_3 (m.d 1 4) (by simp) with h37 | h37
                                      · rcases p20_3 (m.d 2 4) (by simp) with h38 | h38
                                        · linarith only [h38, h8, hlam]
                                        · rcases p20_3 (m.d 3 4) (by simp) with h40 | h40
                                          · linarith only [h40, h9, hlam]
                                          · rcases p20_3 (m.d 4 5) (by simp) with h42 | h42
                                            · linarith only [h11, h42, hlam]
                                            · linarith only [h14, h42, hlam]
                                      · linarith only [h37, h8, hlam]
                                    · linarith only [h36, h4, hlam]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    rcases p20_3 (m.d 0 4) (by simp) with h47 | h47
                                    · rcases p20_3 (m.d 1 4) (by simp) with h48 | h48
                                      · rcases p20_3 (m.d 2 4) (by simp) with h49 | h49
                                        · linarith only [h49, h8, hlam]
                                        · linarith only [h12, h49, hlam]
                                      · linarith only [h48, h9, hlam]
                                    · linarith only [h47, h5, hlam]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h1, h12, h14, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h4, hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h8, hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h14, hc34, hc45, hlam, hphi, p20_1]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h14, hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h5, hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h9, hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h12, hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h18, hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h6, hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h11, hlam, p20_0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [hc24, hlam, hphi, ht45, p20_1, u5elo4]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [h1, h11, h3, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                                  · have p20_0 := h20c.1
                                    have p20_1 := h20c.2.1
                                    have p20_2 := h20c.2.2.1
                                    have p20_3 := h20c.2.2.2
                                    linarith only [hlam, p20_0]
                            · linarith only [h0, h10, h12, h13, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                            · linarith only [h12, h3, h5, h71, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h73 | h73
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h74 | h74
                                · rcases h4bigk with h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h3, h5, hlam, hphi, ht12, p75_1, u1ehi3, u2elo0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h3, h5, h73, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p75_1, u2elo0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h3, h5, h71, h74, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p75_1, u2elo0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    rcases p75_3 (m.d 0 4) (by simp) with h80 | h80
                                    · rcases p75_3 (m.d 1 4) (by simp) with h81 | h81
                                      · linarith only [h1, h81, hlam]
                                      · linarith only [h11, h81, hlam]
                                    · linarith only [h80, hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h1, hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h1, h73, hc01, hc45, hlam, hphi, ht0b, ht5b, p75_1]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h1, h3, h5, h71, h74, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p75_1, u2elo0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    rcases p75_3 (m.d 0 4) (by simp) with h89 | h89
                                    · rcases p75_3 (m.d 1 4) (by simp) with h90 | h90
                                      · rcases p75_3 (m.d 2 4) (by simp) with h91 | h91
                                        · linarith only [h8, h91, hlam]
                                        · linarith only [h73, h91, hlam]
                                      · linarith only [h90, hlam, p75_0]
                                    · linarith only [h6, h89, hlam]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h4, hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h8, hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h12, hlam, p75_1]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p75_1, u2elo0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h5, hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h9, hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h3, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p75_1, u2elo0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h0, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p75_1, u2elo0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h6, hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h11, hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h73, hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [h74, hlam, p75_0]
                                  · have p75_0 := h75c.1
                                    have p75_1 := h75c.2.1
                                    have p75_2 := h75c.2.2.1
                                    have p75_3 := h75c.2.2.2
                                    linarith only [hlam, p75_0]
                                · linarith only [h4, h73, h74, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                                · linarith only [h112, h12, h3, h5, h73, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                                · linarith only [h112, h12, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h11, h3, h5, h6, hlam, hphi, ht12, u1ehi3, u2elo0]
                      · linarith only [h10, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                    · linarith only [h3, h5, h9, hlam, hphi, ht12, u1ehi2, u2elo0]
                  · linarith only [h8, hlam, hphi, ht12, u1ehi1, u2elo3]
                · linarith only [h7, hlam, hphi, ht12, u1ehi1, u2elo2]
              · linarith only [h1, h6, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
              · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                    · linarith only [h1, h122, h124, h5, hlam, hphi, ht12, u1ehi3, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h127 | h127
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                          · linarith only [h0, h122, h124, h126, h128, hlam, hphi, ht12, u1ehi4, u2elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h130 | h130
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h131 | h131
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h132 | h132
                                · rcases h4bigk with h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h124, h126, h4, hlam, hphi, ht12, p133_1, u1ehi4, u2elo0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h128, h130, h132, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p133_1, u2elo0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h5, hlam, p133_1]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    rcases p133_3 (m.d 0 4) (by simp) with h138 | h138
                                    · rcases p133_3 (m.d 1 4) (by simp) with h139 | h139
                                      · linarith only [h1, h139, hlam]
                                      · linarith only [h127, h139, hlam]
                                    · linarith only [h138, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h1, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h1, h128, h130, h132, hc01, hc45, hlam, hphi, ht0b, ht5b, p133_1]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h124, hlam, p133_1]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    rcases p133_3 (m.d 0 4) (by simp) with h147 | h147
                                    · rcases p133_3 (m.d 1 4) (by simp) with h148 | h148
                                      · rcases p133_3 (m.d 2 4) (by simp) with h149 | h149
                                        · linarith only [h123, h149, hlam]
                                        · linarith only [h131, h149, hlam]
                                      · linarith only [h148, hlam, p133_0]
                                    · linarith only [h121, h147, hlam]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h4, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h123, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h128, hlam, p133_1]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p133_1, u2elo0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht12, ht23, p133_1, u1ehi3]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hc34, hlam, hphi, ht12, ht23, p133_1, u1ehi3]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    rcases p133_3 (m.d 0 4) (by simp) with h161 | h161
                                    · linarith only [h161, h5, hlam]
                                    · linarith only [h161, h4, hlam]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    rcases p133_3 (m.d 0 4) (by simp) with h165 | h165
                                    · linarith only [h165, h5, hlam]
                                    · linarith only [h121, h165, hlam]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h121, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h127, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h131, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h132, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hlam, p133_0]
                                · linarith only [h132, h5, hc03, hlam, hphi, ht34, ht45, u5elo4]
                              · linarith only [h1, h127, h128, h130, h131, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h124, h126, h130, hc23, hc34, hlam, hphi]
                        · linarith only [h127, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                      · linarith only [h126, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                  · linarith only [h123, hlam, hphi, ht12, u1ehi1, u2elo3]
                · linarith only [h122, hlam, hphi, ht12, u1ehi1, u2elo2]
              · linarith only [h1, h121, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
          · linarith only [h0, h4, hlam, hphi, ht12, u1ehi1, u2elo3]
        · linarith only [h0, h3, hlam, hphi, ht12, u1ehi1, u2elo2]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · linarith only [h0, hlam, hphi, ht12, u1ehi0, u2elo1]

theorem r1l7_11_12_14_25_L_R_L_R_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h3, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h3, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h11, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                · linarith only [h14, h5, h6, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h16, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h16, h5, h6, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                  · linarith only [h21, h5, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h24, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h20, h21, h23, h24, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h19, h23, h5, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h19, h20, h5, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                  · linarith only [h0, h3, h30, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h19, h30, h32, hc24, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                      · linarith only [h0, h34, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h29, h34, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                  · linarith only [h3, h37, h5, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                    · linarith only [h0, h19, h3, h39, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                      · linarith only [h0, h29, h4, h41, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                        · linarith only [h29, h43, h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                        · linarith only [h43, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
          · linarith only [h3, h47, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
            · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
              · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h55 | h55
                        · linarith only [h1, h49, h55, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h1, h49, h51, h55, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h1, h47, h49, h51, h54, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                    · linarith only [h3, h50, h53, hc15, hlam, hphi, u1ehi1]
                  · linarith only [h3, h52, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                      · linarith only [h51, h61, h63, hc23, hlam, hphi, ht12, u1ehi3]
                      · linarith only [h47, h63, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h3, h62, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h3, h49, h61, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                · linarith only [h49, h50, h68, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                    · linarith only [h49, h50, h71, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h3, h71, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h3, h49, h70, hc13, hlam, hphi, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                  · linarith only [h49, h77, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h3, h77, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h49, h75, h76, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                  · linarith only [h49, h82, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h3, h82, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                  · linarith only [h3, h49, h85, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h3, h85, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h90 | h90
    · linarith only [h0, h90, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h92 | h92
      · linarith only [h0, h92, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
        · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
          · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
            · rcases m.htr 1 3 5 (by decide) (by decide) with h97 | h97
              · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h100 | h100
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h101 | h101
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h102 | h102
                        · linarith only [h102, h94, h99, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h101, h102, h94, h99, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                        · linarith only [h101, h105, hc34, hlam, hphi, ht23, u2ehi3]
                        · rcases h5emax with h107 | h107 | h107 | h107 | h107
                          · linarith only [h101, h107, h92, h94, h96, h98, hc12, hlam, hphi, ht23, ht34, ht45, u1ehi0, u2ehi3]
                          · linarith only [h101, h107, h94, h96, h98, hc12, hlam, hphi, ht23, ht34, ht45, u1ehi4, u2ehi3]
                          · linarith only [h107, hlam, ht23, ht34, ht45, u2ehi4]
                          · linarith only [h105, h107, hlam, ht45, u4ehi3]
                          · linarith only [h101, h107, hlam, ht23, ht34, ht45, u2ehi3]
                    · linarith only [h100, h94, h97, h99, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h114 | h114
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h115 | h115
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h116 | h116
                        · linarith only [h114, h116, h94, h96, h99, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h114, h115, h116, h99, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h114, h115, h99, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                        · rcases h5emax with h122 | h122 | h122 | h122 | h122
                          · linarith only [h114, h121, h122, h92, h94, h96, hc12, hlam, hphi, ht23, ht34, ht45, u1ehi0, u2ehi2]
                          · linarith only [h114, h121, h122, h92, h94, h96, hc12, hlam, hphi, ht23, ht34, ht45, u1ehi0, u2ehi2]
                          · linarith only [h114, h122, hlam, ht23, ht34, ht45, u2ehi2]
                          · linarith only [h114, h122, hlam, ht23, ht34, ht45, u2ehi2]
                          · linarith only [h122, hlam, ht45, u4ehi4]
                        · linarith only [h120, h121, h95, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                        · linarith only [h120, h129, h94, h96, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h129, h99, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h133 | h133
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                      · linarith only [h134, h98, hc24, hlam, hphi, ht12, u1ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h136 | h136
                        · linarith only [h132, h136, h92, h98, hc23, hlam, hphi, ht12, u1ehi0]
                        · rcases h5emax with h138 | h138 | h138 | h138 | h138
                          · linarith only [h138, h92, hlam, ht12, ht23, ht34, ht45, u1ehi0]
                          · linarith only [h138, h92, hlam, ht12, ht23, ht34, ht45, u1ehi0]
                          · linarith only [h138, hlam, ht23, ht34, ht45, u2ehi4]
                          · linarith only [h136, h138, hlam, ht45, u4ehi3]
                          · linarith only [h138, h92, h98, hlam, ht12, ht23, ht34, ht45, u1ehi0]
                    · linarith only [h132, h133, h94, h97, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h132, h96, h98, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h90, h97, hc35, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h90, h96, hc34, hlam, hphi, ht12, ht23, u1ehi0]
          · linarith only [h90, h94, h95, hc24, hlam, hphi, ht12, u1ehi0]
        · linarith only [h0, h94, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
