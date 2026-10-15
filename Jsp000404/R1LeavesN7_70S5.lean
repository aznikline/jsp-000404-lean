import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_L_L_I_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h4, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h11, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14 | h14
                · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h15, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h18, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h21 | h21
              · linarith only [h21, h4, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h23 | h23
                · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h24, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h24, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                  · linarith only [h0, h27, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h23, h27, h3, h4, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h30 | h30
            · rcases m.htr 0 3 4 (by decide) (by decide) with h31 | h31
              · rcases m.htr 0 4 5 (by decide) (by decide) with h32 | h32
                · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
                  · linarith only [h0, h33, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                    · linarith only [h1, h33, h35, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h30, h35, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                  · linarith only [h0, h38, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                    · linarith only [h1, h38, h40, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h30, h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h30, h31, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h44 | h44
              · rcases m.htr 0 4 5 (by decide) (by decide) with h45 | h45
                · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                  · linarith only [h0, h46, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
                    · linarith only [h1, h30, h46, h48, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                      · linarith only [h0, h50, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                        · linarith only [h1, h52, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h44, h46, h52, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
                  · linarith only [h0, h4, h55, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
                    · linarith only [h0, h30, h57, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                      · linarith only [h0, h59, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                        · linarith only [h1, h61, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h44, h55, h61, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h64 | h64
                · rcases m.htr 1 2 3 (by decide) (by decide) with h65 | h65
                  · linarith only [h0, h65, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h67 | h67
                    · linarith only [h0, h30, h67, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h69 | h69
                      · linarith only [h0, h69, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                        · linarith only [h1, h4, h44, h71, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
                          · linarith only [h1, h73, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                            · linarith only [h2, h75, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h64, h71, h75, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                  · linarith only [h0, h4, h78, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                    · linarith only [h0, h30, h80, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
                      · linarith only [h1, h78, h82, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                        · linarith only [h1, h44, h84, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                          · linarith only [h2, h84, h86, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h88 | h88
                            · linarith only [h2, h44, h64, h88, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                              · linarith only [h1, h44, h78, h90, hc12, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h4, h90, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h93 | h93
          · rcases m.htr 0 2 4 (by decide) (by decide) with h94 | h94
            · rcases m.htr 0 3 4 (by decide) (by decide) with h95 | h95
              · rcases m.htr 0 4 5 (by decide) (by decide) with h96 | h96
                · linarith only [h2, h3, h96, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
                  · linarith only [h0, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h93, h98, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                  · linarith only [h0, h103, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h103, h3, h93, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h106 | h106
              · linarith only [h106, h93, h94, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
                · linarith only [h108, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
                  · linarith only [h0, h110, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h110, h93, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h113 | h113
            · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
              · rcases m.htr 0 4 5 (by decide) (by decide) with h115 | h115
                · linarith only [h0, h113, h115, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
                  · linarith only [h0, h117, h93, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
                    · linarith only [h0, h119, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h113, h119, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h113, h114, h93, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
              · rcases m.htr 0 4 5 (by decide) (by decide) with h124 | h124
                · linarith only [h1, h123, h124, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
                  · linarith only [h0, h126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                    · linarith only [h113, h126, h128, hc02, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                      · linarith only [h1, h126, h130, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                        · linarith only [h1, h132, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h123, h132, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h135 | h135
                · linarith only [h135, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                  · linarith only [h0, h137, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
                    · linarith only [h113, h137, h139, hc02, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h141 | h141
                      · linarith only [h0, h141, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                        · linarith only [h1, h123, h143, h3, h93, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h145 | h145
                          · linarith only [h1, h145, h3, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                          · linarith only [h143, h145, h2, h3, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h148 | h148
        · rcases m.htr 0 2 3 (by decide) (by decide) with h149 | h149
          · rcases m.htr 0 2 4 (by decide) (by decide) with h150 | h150
            · linarith only [h0, h150, h2, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h152 | h152
              · linarith only [h1, h152, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h154 | h154
                · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                  · linarith only [h0, h155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h149, h155, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h148, h154, h2, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h159 | h159
            · linarith only [h0, h159, h2, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h161 | h161
              · linarith only [h1, h161, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h163 | h163
                · rcases m.htr 1 2 3 (by decide) (by decide) with h164 | h164
                  · linarith only [h0, h164, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h166 | h166
                    · linarith only [h159, h164, h166, hc02, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
                      · linarith only [h0, h168, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                        · linarith only [h1, h161, h170, h2, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1, h164, h170, h2, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h148, h163, h2, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h174 | h174
          · rcases m.htr 0 2 4 (by decide) (by decide) with h175 | h175
            · linarith only [h0, h175, h2, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h177 | h177
              · linarith only [h1, h177, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h179 | h179
                · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
                  · linarith only [h0, h148, h179, h180, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h148, h174, h179, h180, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                  · linarith only [h0, h183, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h174, h179, h183, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h186 | h186
            · linarith only [h0, h186, h2, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h188 | h188
              · linarith only [h1, h188, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h190 | h190
                · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                  · linarith only [h0, h191, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h193 | h193
                    · linarith only [h186, h191, h193, hc02, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h195 | h195
                      · linarith only [h0, h148, h190, h195, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                        · linarith only [h1, h148, h188, h190, h197, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1, h191, h197, h2, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h200 | h200
                  · linarith only [h0, h174, h200, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h202 | h202
                    · linarith only [h1, h190, h2, h200, h202, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h204 | h204
                      · linarith only [h1, h190, h2, h200, h204, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                        · linarith only [h1, h190, h2, h206, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h1, h2, h200, h206, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h210 | h210
    · rcases m.htr 0 1 4 (by decide) (by decide) with h211 | h211
      · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
        · rcases m.htr 0 2 3 (by decide) (by decide) with h213 | h213
          · rcases m.htr 0 2 4 (by decide) (by decide) with h214 | h214
            · rcases m.htr 0 3 4 (by decide) (by decide) with h215 | h215
              · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
                · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h219 | h219
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h220 | h220
                        · linarith only [h210, h220, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h215, h220, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h212, h219, hlam]
                    · linarith only [h0, h214, h218, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h210, h217, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h227 | h227
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h228 | h228
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                        · linarith only [h210, h229, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h215, h229, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h212, h228, hlam]
                    · linarith only [h0, h214, h227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h210, h226, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h235 | h235
                · rcases m.htr 1 2 3 (by decide) (by decide) with h236 | h236
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
                        · linarith only [h210, h215, h239, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h241 | h241
                          · linarith only [h211, h239, h241, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
                            · linarith only [h0, h211, h243, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h235, h239, h243, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h212, h238, hlam]
                    · linarith only [h0, h214, h237, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h210, h236, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h249 | h249
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h251 | h251
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h252 | h252
                        · linarith only [h210, h215, h252, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h254 | h254
                          · linarith only [h211, h252, h254, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h256 | h256
                            · linarith only [h0, h211, h235, h256, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h258 | h258
                              · linarith only [h210, h215, h249, h258, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                                · linarith only [h249, h254, h260, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h262 | h262
                                  · linarith only [h214, h235, h262, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h264 | h264
                                    · linarith only [h211, h235, h249, h252, h264, hc23, hlam, hphi, u3elo3]
                                    · rcases h1bigk with h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [hlam, p266_0]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h0, hlam, p266_0]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h249, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u0elo0]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h0, h249, h252, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u0elo1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h0, h249, h252, h256, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u0elo1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        rcases p266_3 (m.d 0 1) (by simp) with h272 | h272
                                        · linarith only [h272, hlam, p266_0]
                                        · rcases p266_3 (m.d 1 2) (by simp) with h274 | h274
                                          · rcases p266_3 (m.d 1 3) (by simp) with h275 | h275
                                            · linarith only [h249, h275, hlam]
                                            · rcases p266_3 (m.d 1 4) (by simp) with h277 | h277
                                              · linarith only [h250, h277, hlam]
                                              · rcases p266_3 (m.d 1 5) (by simp) with h279 | h279
                                                · linarith only [h251, h279, hlam]
                                                · rcases h4bigk with h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [hlam, p281_0]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h249, h252, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1, u0elo3]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h0, h211, hc24, hlam, hphi, ht0b, ht45, ht5b, p281_1, u0elo1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h215, hlam, p281_0]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h235, hlam, p281_0]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h211, hlam, p281_1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [hlam, p281_0]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h0, h211, hc24, hlam, hphi, ht0b, ht45, ht5b, p281_1, u0elo1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h252, hlam, p281_1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h256, hlam, p281_0]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h214, hlam, p281_1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h250, hlam, p281_1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [hlam, p281_0]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h258, hlam, p281_1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h262, hlam, p281_0]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h264, hc04, hc45, hlam, hphi, p281_1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h250, h264, hc24, hc45, hlam, hphi, p281_1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h264, hc24, hc45, hlam, hphi, p281_1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [hlam, p281_0]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h264, hlam, p281_0]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    rcases p281_3 (m.d 0 4) (by simp) with h302 | h302
                                                    · linarith only [h302, hlam, p281_0]
                                                    · rcases p281_3 (m.d 1 4) (by simp) with h304 | h304
                                                      · linarith only [h256, h304, hlam]
                                                      · rcases p281_3 (m.d 2 4) (by simp) with h306 | h306
                                                        · linarith only [h262, h306, hlam]
                                                        · rcases p281_3 (m.d 3 4) (by simp) with h308 | h308
                                                          · linarith only [h264, h308, hlam]
                                                          · linarith only [h215, h308, hlam]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    rcases p281_3 (m.d 0 4) (by simp) with h311 | h311
                                                    · linarith only [h235, h311, hlam]
                                                    · linarith only [h211, h311, hlam]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    rcases p281_3 (m.d 0 4) (by simp) with h314 | h314
                                                    · linarith only [h235, h314, hlam]
                                                    · linarith only [h214, h314, hlam]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [h210, h215, h249, hc23, hc45, hlam, hphi, ht34, p281_1]
                                                  · have p281_0 := h281c.1
                                                    have p281_1 := h281c.2.1
                                                    have p281_2 := h281c.2.2.1
                                                    have p281_3 := h281c.2.2.2
                                                    linarith only [hlam, p281_0]
                                          · linarith only [h274, hlam, p266_0]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [hlam, p266_0]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        rcases p266_3 (m.d 0 1) (by simp) with h321 | h321
                                        · linarith only [h0, h321, hlam]
                                        · linarith only [h210, h321, hlam]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        rcases p266_3 (m.d 0 1) (by simp) with h324 | h324
                                        · linarith only [h0, h324, hlam]
                                        · linarith only [h211, h324, hlam]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        rcases p266_3 (m.d 0 1) (by simp) with h327 | h327
                                        · linarith only [h0, h327, hlam]
                                        · linarith only [h212, h327, hlam]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h210, hlam, p266_0]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h249, hlam, p266_1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [hlam, p266_0]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h252, hlam, p266_1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h254, hlam, p266_1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h211, hlam, p266_0]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h250, hlam, p266_1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h0, h211, h249, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u0elo1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [hlam, p266_0]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h256, hlam, p266_1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h212, hlam, p266_0]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h251, hlam, p266_1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h0, h212, h249, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u0elo1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [h0, h212, hc14, hlam, hphi, ht0b, ht45, ht5b, p266_1, u0elo1]
                                      · have p266_0 := h266c.1
                                        have p266_1 := h266c.2.1
                                        have p266_2 := h266c.2.2.1
                                        have p266_3 := h266c.2.2.2
                                        linarith only [hlam, p266_0]
                      · linarith only [h0, h212, h251, hlam]
                    · linarith only [h0, h214, h250, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h210, h249, hc13, hlam, hphi, u3elo2]
            · linarith only [h0, h211, h214, hlam]
          · linarith only [h0, h210, h213, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h350 | h350
          · rcases m.htr 0 2 4 (by decide) (by decide) with h351 | h351
            · rcases m.htr 0 3 4 (by decide) (by decide) with h352 | h352
              · rcases m.htr 0 4 5 (by decide) (by decide) with h353 | h353
                · linarith only [h210, h212, h352, h353, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h355 | h355
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h356 | h356
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h357 | h357
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h358 | h358
                        · linarith only [h210, h358, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h210, h352, h358, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h361 | h361
                        · linarith only [h0, h210, h357, h361, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h210, h352, h357, h361, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h351, h356, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h210, h355, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h366 | h366
                · linarith only [h211, h212, h366, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h368 | h368
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h369 | h369
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h370 | h370
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
                        · linarith only [h210, h352, h371, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h373 | h373
                          · linarith only [h210, h212, h373, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                          · linarith only [h211, h212, h368, h371, h373, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
                        · linarith only [h352, h376, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h378 | h378
                          · linarith only [h0, h211, h370, h376, h378, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h211, h370, h376, h378, hc13, hlam, hphi, u3elo4]
                    · linarith only [h0, h351, h369, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h210, h368, hc13, hlam, hphi, u3elo2]
            · linarith only [h0, h211, h351, hlam]
          · linarith only [h0, h210, h350, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h385 | h385
        · rcases m.htr 0 2 3 (by decide) (by decide) with h386 | h386
          · rcases m.htr 0 2 4 (by decide) (by decide) with h387 | h387
            · rcases m.htr 0 3 4 (by decide) (by decide) with h388 | h388
              · linarith only [h210, h211, h388, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h390 | h390
                · rcases m.htr 1 2 3 (by decide) (by decide) with h391 | h391
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h392 | h392
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h393 | h393
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h394 | h394
                        · linarith only [h210, h388, h394, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h210, h211, h394, hc13, hlam, hphi, u3elo3]
                      · linarith only [h211, h385, h392, h393, hlam]
                    · linarith only [h387, h392, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h391, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h211, h385, h390, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h401 | h401
              · linarith only [h0, h210, h387, h401, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h403 | h403
                · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h406 | h406
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                        · linarith only [h0, h210, h387, h401, h407, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h0, h210, h387, h405, h407, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h210, h387, h404, h405, h406, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h411 | h411
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h412 | h412
                        · linarith only [h210, h412, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h210, h405, h412, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h385, h411, hlam]
                  · linarith only [h0, h404, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h0, h385, h387, h403, hlam]
          · linarith only [h0, h210, h386, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h419 | h419
          · rcases m.htr 0 2 4 (by decide) (by decide) with h420 | h420
            · rcases m.htr 0 3 4 (by decide) (by decide) with h421 | h421
              · linarith only [h210, h211, h421, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h423 | h423
                · rcases m.htr 1 2 3 (by decide) (by decide) with h424 | h424
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h425 | h425
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h426 | h426
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                        · linarith only [h210, h421, h427, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h210, h211, h427, hc13, hlam, hphi, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h430 | h430
                        · linarith only [h210, h385, h420, h423, h430, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h210, h211, h424, h430, hc23, hlam, hphi, u3elo3]
                    · linarith only [h420, h425, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h210, h424, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h435 | h435
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h436 | h436
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h437 | h437
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h438 | h438
                        · linarith only [h210, h438, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h210, h211, h438, hc13, hlam, hphi, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h441 | h441
                        · linarith only [h210, h211, h436, h437, h441, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h210, h211, h435, h441, hc23, hlam, hphi, u3elo3]
                    · linarith only [h420, h436, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h210, h435, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h446 | h446
              · linarith only [h0, h210, h420, h446, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h448 | h448
                · rcases m.htr 1 2 3 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h450 | h450
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h451 | h451
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h452 | h452
                        · linarith only [h210, h446, h452, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h210, h420, h450, h452, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h210, h420, h449, h450, h451, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h456 | h456
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h457 | h457
                        · linarith only [h210, h457, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h210, h385, h449, h450, h456, h457, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                        · linarith only [h210, h460, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h210, h449, h450, h460, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h449, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h465 | h465
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h466 | h466
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h467 | h467
                        · linarith only [h210, h467, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h210, h211, h467, hc13, hlam, hphi, u3elo3]
                      · linarith only [h420, h465, h466, hc02, hc25, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h471 | h471
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h472 | h472
                        · linarith only [h210, h446, h472, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h210, h464, h465, h472, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h475 | h475
                        · linarith only [h210, h475, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h210, h465, h475, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h210, h464, hc13, hlam, hphi, u3elo2]
          · linarith only [h0, h210, h419, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h480 | h480
      · rcases m.htr 0 1 5 (by decide) (by decide) with h481 | h481
        · rcases m.htr 0 2 3 (by decide) (by decide) with h482 | h482
          · rcases m.htr 0 2 4 (by decide) (by decide) with h483 | h483
            · rcases m.htr 0 3 4 (by decide) (by decide) with h484 | h484
              · rcases m.htr 0 4 5 (by decide) (by decide) with h485 | h485
                · rcases m.htr 1 2 3 (by decide) (by decide) with h486 | h486
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h487 | h487
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h488 | h488
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h489 | h489
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h490 | h490
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
                            · linarith only [h210, h480, h491, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h210, h480, h485, h491, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h210, h490, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h210, h480, h482, h484, h487, h489, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h210, h481, h486, h488, hlam]
                    · linarith only [h210, h483, h486, h487, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h482, h486, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h501 | h501
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h502 | h502
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h503 | h503
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h504 | h504
                            · linarith only [h480, h485, h504, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h506 | h506
                              · linarith only [h482, h506, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h482, h484, h506, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h210, h503, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h210, h480, h500, h502, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h210, h481, h499, h501, hlam]
                    · linarith only [h210, h483, h499, h500, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h480, h499, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h210, h480, h484, hlam]
            · linarith only [h210, h480, h482, h483, hc23, hlam, hphi, u3elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h516 | h516
            · rcases m.htr 0 3 4 (by decide) (by decide) with h517 | h517
              · rcases m.htr 0 4 5 (by decide) (by decide) with h518 | h518
                · rcases m.htr 1 2 3 (by decide) (by decide) with h519 | h519
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h520 | h520
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h521 | h521
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h522 | h522
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h523 | h523
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h524 | h524
                            · linarith only [h0, h480, h482, h519, h524, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h518, h524, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h0, h482, h519, h523, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h480, h482, h519, h520, h522, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h480, h482, h519, h520, h521, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h480, h482, h519, h520, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h480, h519, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h532 | h532
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h533 | h533
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h534 | h534
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h535 | h535
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h537 | h537
                            · linarith only [h480, h518, h537, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h539 | h539
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h540 | h540
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h541 | h541
                                  · linarith only [h0, h480, h482, h518, h532, h533, h541, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h543 | h543
                                    · linarith only [h480, h518, h533, h539, h543, hlam]
                                    · rcases h1bigk with h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h0, hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h210, hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h0, h482, h532, h533, h539, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p545_1, u3elo1]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h0, h482, h532, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p545_1, u3elo1]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        rcases p545_3 (m.d 0 1) (by simp) with h551 | h551
                                        · linarith only [h551, hlam, p545_0]
                                        · rcases p545_3 (m.d 1 2) (by simp) with h553 | h553
                                          · rcases p545_3 (m.d 1 3) (by simp) with h554 | h554
                                            · linarith only [h532, h554, hlam]
                                            · linarith only [h210, h554, hlam]
                                          · linarith only [h553, hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h0, h482, h532, hc01, hc12, hlam, hphi, p545_1]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h0, h481, h482, h532, h537, hlam, p545_2]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h0, h481, h482, h532, hlam, p545_2]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h481, h533, h537, h539, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p545_1, u3elo1]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h532, hlam, p545_1]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        rcases p545_3 (m.d 0 1) (by simp) with h565 | h565
                                        · linarith only [h210, h565, hlam]
                                        · linarith only [h480, h565, hlam]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        rcases p545_3 (m.d 0 1) (by simp) with h568 | h568
                                        · linarith only [h210, h568, hlam]
                                        · linarith only [h481, h568, hlam]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h480, hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h533, hlam, p545_1]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h535, hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h537, hlam, p545_1]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h481, hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h534, hlam, p545_1]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h536, hlam, p545_0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [h481, h533, h539, hc34, hlam, hphi, ht0b, ht45, ht5b, p545_1, u0elo0]
                                      · have p545_0 := h545c.1
                                        have p545_1 := h545c.2.1
                                        have p545_2 := h545c.2.2.1
                                        have p545_3 := h545c.2.2.2
                                        linarith only [hlam, p545_0]
                                · linarith only [h0, h482, h540, hc01, hlam, hphi, ht12, ht23, u3elo4]
                              · linarith only [h0, h482, h539, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h210, h480, h533, h536, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h480, h482, h532, h533, h535, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h480, h482, h532, h533, h534, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h480, h482, h532, h533, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h480, h532, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h210, h480, h517, hlam]
            · linarith only [h0, h480, h516, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h590 | h590
          · rcases m.htr 0 2 4 (by decide) (by decide) with h591 | h591
            · rcases m.htr 0 3 4 (by decide) (by decide) with h592 | h592
              · rcases m.htr 0 4 5 (by decide) (by decide) with h593 | h593
                · linarith only [h480, h481, h593, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h596 | h596
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h597 | h597
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h598 | h598
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h599 | h599
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h600 | h600
                            · linarith only [h480, h593, h600, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h602 | h602
                              · linarith only [h590, h602, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h590, h592, h602, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h210, h480, h596, h599, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h210, h480, h596, h598, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h607 | h607
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h608 | h608
                          · linarith only [h595, h597, h608, hlam]
                          · linarith only [h210, h480, h596, h608, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h210, h480, h596, h607, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h210, h591, h595, h596, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h480, h595, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h210, h480, h592, hlam]
            · linarith only [h210, h480, h590, h591, hc23, hlam, hphi, u3elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h616 | h616
            · rcases m.htr 0 3 4 (by decide) (by decide) with h617 | h617
              · rcases m.htr 0 4 5 (by decide) (by decide) with h618 | h618
                · linarith only [h480, h481, h618, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h621 | h621
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h622 | h622
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h623 | h623
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h624 | h624
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h625 | h625
                            · linarith only [h0, h480, h590, h618, h620, h625, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h627 | h627
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h628 | h628
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h629 | h629
                                  · linarith only [h0, h480, h590, h620, h621, h625, h629, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h631 | h631
                                    · linarith only [h480, h481, h621, h625, h627, h631, hlam]
                                    · rcases h1bigk with h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h0, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h210, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h0, h590, h620, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p633_1, u3elo1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h481, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        rcases p633_3 (m.d 0 1) (by simp) with h639 | h639
                                        · linarith only [h639, hlam, p633_0]
                                        · rcases p633_3 (m.d 1 2) (by simp) with h641 | h641
                                          · rcases p633_3 (m.d 1 3) (by simp) with h642 | h642
                                            · linarith only [h620, h642, hlam]
                                            · linarith only [h210, h642, hlam]
                                          · linarith only [h641, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h0, h590, h620, hc01, hc12, hlam, hphi, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h0, h480, h590, h620, hlam, p633_2]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h480, h481, h621, h627, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h480, h621, h627, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p633_1, u3elo1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h620, hlam, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        rcases p633_3 (m.d 0 1) (by simp) with h653 | h653
                                        · linarith only [h210, h653, hlam]
                                        · linarith only [h480, h653, hlam]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h480, h481, h621, h627, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p633_1, u3elo1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h480, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h621, hlam, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h623, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h625, hlam, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h480, h621, h625, h627, hc34, hc45, hlam, hphi, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h622, hlam, p633_1]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [h624, hlam, p633_0]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        rcases p633_3 (m.d 0 1) (by simp) with h665 | h665
                                        · linarith only [h481, h665, hlam]
                                        · linarith only [h480, h665, hlam]
                                      · have p633_0 := h633c.1
                                        have p633_1 := h633c.2.1
                                        have p633_2 := h633c.2.2.1
                                        have p633_3 := h633c.2.2.2
                                        linarith only [hlam, p633_0]
                                · linarith only [h0, h480, h590, h621, h627, h628, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · linarith only [h0, h480, h590, h621, h627, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h210, h480, h621, h624, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h480, h590, h620, h621, h623, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h480, h590, h620, h621, h622, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h590, h620, h621, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h480, h620, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h0, h480, h590, h617, hlam]
            · linarith only [h0, h480, h616, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h678 | h678
        · rcases m.htr 0 2 3 (by decide) (by decide) with h679 | h679
          · rcases m.htr 0 2 4 (by decide) (by decide) with h680 | h680
            · rcases m.htr 0 3 4 (by decide) (by decide) with h681 | h681
              · rcases m.htr 0 4 5 (by decide) (by decide) with h682 | h682
                · rcases m.htr 1 2 3 (by decide) (by decide) with h683 | h683
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h684 | h684
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h685 | h685
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h686 | h686
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h687 | h687
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h688 | h688
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h689 | h689
                              · linarith only [h679, h689, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h681, h689, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h480, h678, h682, h685, h688, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h480, h678, h685, h686, h687, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h679, h681, h686, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h480, h678, h684, h685, hlam]
                    · linarith only [h680, h684, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h678, h683, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h480, h678, h682, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h699 | h699
                · rcases m.htr 1 2 3 (by decide) (by decide) with h700 | h700
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h701 | h701
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h702 | h702
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h703 | h703
                        · linarith only [h681, h703, hc03, hlam, hphi, u3elo1]
                        · linarith only [h210, h678, h702, h703, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h210, h678, h700, h702, hlam]
                    · linarith only [h210, h680, h700, h701, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h679, h700, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h210, h678, h681, h699, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h710 | h710
              · linarith only [h679, h680, h710, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h712 | h712
                · rcases m.htr 1 2 3 (by decide) (by decide) with h713 | h713
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h714 | h714
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h715 | h715
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h716 | h716
                        · linarith only [h710, h716, hc03, hlam, hphi, u3elo1]
                        · linarith only [h210, h678, h715, h716, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h680, h714, h715, hc02, hc25, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h720 | h720
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h721 | h721
                        · linarith only [h210, h710, h721, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h210, h678, h720, h721, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h210, h678, h720, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h713, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h480, h678, h712, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h727 | h727
            · rcases m.htr 0 3 4 (by decide) (by decide) with h728 | h728
              · rcases m.htr 0 4 5 (by decide) (by decide) with h729 | h729
                · rcases m.htr 1 2 3 (by decide) (by decide) with h730 | h730
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h731 | h731
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h732 | h732
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h733 | h733
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h734 | h734
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h735 | h735
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h736 | h736
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h737 | h737
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h738 | h738
                                  · linarith only [h727, h738, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h679, h727, h729, h730, h738, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h480, h679, h727, h737, hc01, hlam, hphi, ht12, ht23, u3elo4]
                              · linarith only [h480, h679, h727, h736, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h727, h729, h735, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h480, h679, h727, h730, h734, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h480, h678, h679, h727, h728, h730, h732, h733, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h480, h679, h727, h730, h732, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h679, h727, h730, h731, hlam]
                  · linarith only [h0, h678, h730, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h480, h678, h729, hlam]
              · linarith only [h679, h727, h728, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h751 | h751
              · rcases m.htr 0 4 5 (by decide) (by decide) with h752 | h752
                · rcases m.htr 1 2 3 (by decide) (by decide) with h753 | h753
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h754 | h754
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h755 | h755
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h756 | h756
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h757 | h757
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h758 | h758
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h759 | h759
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h760 | h760
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h761 | h761
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h762 | h762
                                    · linarith only [h751, h762, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                    · linarith only [h752, h762, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                  · linarith only [h678, h727, h758, h761, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                · linarith only [h0, h678, h679, h755, h760, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                              · linarith only [h0, h678, h679, h755, h759, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · linarith only [h0, h678, h727, h751, h752, h754, h755, h758, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h210, h678, h755, h757, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h0, h678, h679, h751, h753, h755, h756, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h0, h679, h753, h755, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h678, h679, h753, h754, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h678, h753, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h480, h678, h752, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h775 | h775
                · rcases m.htr 1 2 3 (by decide) (by decide) with h776 | h776
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h777 | h777
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h778 | h778
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h779 | h779
                        · linarith only [h0, h678, h679, h751, h778, h779, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h210, h678, h778, h779, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h0, h679, h776, h778, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h678, h679, h776, h777, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h678, h776, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h0, h678, h679, h751, h775, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h786 | h786
          · rcases m.htr 0 2 4 (by decide) (by decide) with h787 | h787
            · rcases m.htr 0 3 4 (by decide) (by decide) with h788 | h788
              · rcases m.htr 0 4 5 (by decide) (by decide) with h789 | h789
                · rcases m.htr 1 2 3 (by decide) (by decide) with h790 | h790
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h791 | h791
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h792 | h792
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h793 | h793
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h794 | h794
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h795 | h795
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h796 | h796
                              · linarith only [h786, h796, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h788, h796, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h789, h795, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h210, h794, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h210, h786, h788, h793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h802 | h802
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h803 | h803
                          · linarith only [h790, h792, h803, hlam]
                          · linarith only [h210, h803, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h210, h788, h802, hlam]
                    · linarith only [h0, h787, h791, hlam]
                  · linarith only [h0, h790, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h809 | h809
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h810 | h810
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h811 | h811
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h812 | h812
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h813 | h813
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h814 | h814
                            · linarith only [h480, h789, h812, h814, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h816 | h816
                              · linarith only [h786, h816, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h786, h788, h816, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h210, h813, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h210, h786, h788, h812, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h821 | h821
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h822 | h822
                          · linarith only [h809, h811, h822, hlam]
                          · linarith only [h210, h822, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h210, h788, h821, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h787, h810, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h809, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h828 | h828
                · rcases m.htr 1 2 3 (by decide) (by decide) with h829 | h829
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h830 | h830
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h831 | h831
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h832 | h832
                        · linarith only [h788, h832, hc03, hlam, hphi, u3elo1]
                        · linarith only [h210, h832, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h835 | h835
                        · linarith only [h210, h788, h829, h831, h835, hc01, hc25, hlam, hphi, ht12]
                        · linarith only [h210, h835, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h787, h830, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h786, h829, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h840 | h840
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h841 | h841
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h842 | h842
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h843 | h843
                        · linarith only [h210, h788, h843, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h210, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h846 | h846
                        · linarith only [h210, h788, h846, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h210, h846, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h787, h841, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h840, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h851 | h851
              · linarith only [h786, h787, h851, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h853 | h853
                · rcases m.htr 1 2 3 (by decide) (by decide) with h854 | h854
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h855 | h855
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h856 | h856
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h857 | h857
                        · linarith only [h851, h857, hc03, hlam, hphi, u3elo1]
                        · linarith only [h210, h857, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h787, h855, h856, hc02, hc25, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h861 | h861
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h862 | h862
                        · linarith only [h210, h851, h862, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h210, h862, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h865 | h865
                        · linarith only [h210, h851, h865, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h210, h865, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h786, h854, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h869 | h869
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h870 | h870
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h871 | h871
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h872 | h872
                        · linarith only [h210, h851, h872, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h210, h872, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h787, h870, h871, hc02, hc25, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h876 | h876
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h877 | h877
                        · linarith only [h210, h851, h877, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h210, h877, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h880 | h880
                        · linarith only [h210, h851, h880, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h210, h880, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h786, h869, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h884 | h884
            · rcases m.htr 0 3 4 (by decide) (by decide) with h885 | h885
              · rcases m.htr 0 4 5 (by decide) (by decide) with h886 | h886
                · rcases m.htr 1 2 3 (by decide) (by decide) with h887 | h887
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h888 | h888
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h889 | h889
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h890 | h890
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h891 | h891
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h892 | h892
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h893 | h893
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h894 | h894
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h895 | h895
                                  · linarith only [h786, h884, h887, h895, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                  · linarith only [h786, h884, h886, h887, h893, h895, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h786, h894, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h786, h884, h886, h893, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · linarith only [h884, h886, h892, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h786, h887, h891, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h786, h884, h885, h887, h890, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h786, h884, h887, h889, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h786, h884, h887, h888, hlam]
                  · linarith only [h0, h887, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h906 | h906
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h907 | h907
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h908 | h908
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h909 | h909
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h910 | h910
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h911 | h911
                            · linarith only [h480, h886, h909, h911, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h913 | h913
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h914 | h914
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h915 | h915
                                  · linarith only [h884, h911, h915, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h917 | h917
                                    · linarith only [h480, h911, h917, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                    · rcases h1bigk with h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h0, hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h210, hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h480, hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h678, hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        rcases p919_3 (m.d 0 1) (by simp) with h925 | h925
                                        · linarith only [h925, hlam, p919_0]
                                        · rcases p919_3 (m.d 1 2) (by simp) with h927 | h927
                                          · rcases p919_3 (m.d 1 3) (by simp) with h928 | h928
                                            · linarith only [h906, h928, hlam]
                                            · linarith only [h210, h928, hlam]
                                          · linarith only [h927, hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h786, h884, h906, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h480, hc01, hc12, hlam, hphi, p919_1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h678, hc01, hc12, hlam, hphi, p919_1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p919_1, u3elo1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h906, hlam, p919_1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h480, hc01, hlam, hphi, ht12, ht23, p919_1, u3elo1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h678, hc01, hlam, hphi, ht12, ht23, p919_1, u3elo1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h911, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p919_1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h907, hlam, p919_1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h909, hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h911, hlam, p919_1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h910, hc01, hlam, hphi, ht12, ht23, p919_1, u3elo1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h908, hlam, p919_1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h910, hlam, p919_0]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [h480, h910, hc01, hlam, hphi, ht12, ht23, p919_1, u3elo1]
                                      · have p919_0 := h919c.1
                                        have p919_1 := h919c.2.1
                                        have p919_2 := h919c.2.2.1
                                        have p919_3 := h919c.2.2.2
                                        linarith only [hlam, p919_0]
                                · linarith only [h786, h884, h913, h914, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · linarith only [h786, h884, h913, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h210, h910, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h786, h884, h885, h906, h909, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h786, h884, h906, h908, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h786, h884, h906, h907, hlam]
                  · linarith only [h0, h906, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h786, h884, h885, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h959 | h959
              · rcases m.htr 0 4 5 (by decide) (by decide) with h960 | h960
                · rcases m.htr 1 2 3 (by decide) (by decide) with h961 | h961
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h962 | h962
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h963 | h963
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h964 | h964
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h965 | h965
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h966 | h966
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h967 | h967
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h968 | h968
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h969 | h969
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h970 | h970
                                    · linarith only [h959, h970, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                    · linarith only [h960, h970, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                  · linarith only [h884, h959, h960, h969, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h0, h786, h968, hc01, hlam, hphi, ht12, ht23, u3elo4]
                              · linarith only [h786, h959, h967, hlam]
                            · linarith only [h959, h960, h966, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h210, h965, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h786, h959, h961, h964, hlam]
                      · linarith only [h0, h786, h961, h963, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h786, h961, h962, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h961, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h982 | h982
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h983 | h983
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h984 | h984
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h985 | h985
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h986 | h986
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h987 | h987
                            · linarith only [h480, h960, h985, h987, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h989 | h989
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h990 | h990
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h991 | h991
                                  · linarith only [h983, h987, h991, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h993 | h993
                                    · linarith only [h959, h987, h993, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · rcases h1bigk with h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h0, hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h210, hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h480, hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h678, hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        rcases p995_3 (m.d 0 1) (by simp) with h1001 | h1001
                                        · linarith only [h1001, hlam, p995_0]
                                        · rcases p995_3 (m.d 1 2) (by simp) with h1003 | h1003
                                          · rcases p995_3 (m.d 1 3) (by simp) with h1004 | h1004
                                            · linarith only [h1004, h982, hlam]
                                            · linarith only [h1004, h210, hlam]
                                          · linarith only [h1003, hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h210, hc01, hc12, hlam, hphi, p995_1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h0, h884, h983, hc01, hc12, hlam, hphi, p995_1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h0, h884, h983, h987, hc01, hc12, hlam, hphi, p995_1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p995_1, u3elo1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h982, hlam, p995_1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h0, h884, h983, hc01, hlam, hphi, ht12, ht23, p995_1, u3elo1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h0, h884, h983, h987, hc01, hlam, hphi, ht12, ht23, p995_1, u3elo1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h987, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p995_1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h983, hlam, p995_1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h985, hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h987, hlam, p995_1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h986, hc01, hlam, hphi, ht12, ht23, p995_1, u3elo1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h984, hlam, p995_1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h986, hlam, p995_0]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [h480, h986, hc01, hlam, hphi, ht12, ht23, p995_1, u3elo1]
                                      · have p995_0 := h995c.1
                                        have p995_1 := h995c.2.1
                                        have p995_2 := h995c.2.2.1
                                        have p995_3 := h995c.2.2.2
                                        linarith only [hlam, p995_0]
                                · linarith only [h0, h884, h989, h990, hc01, hlam, hphi, ht12, ht23, u3elo4]
                              · linarith only [h786, h959, h989, hlam]
                          · linarith only [h210, h986, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h786, h959, h982, h985, hlam]
                      · linarith only [h0, h786, h982, h984, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h786, h982, h983, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h982, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1034 | h1034
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1035 | h1035
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1036 | h1036
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1037 | h1037
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1038 | h1038
                        · linarith only [h1038, h959, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1038, h210, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1035, h1037, h786, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1035, h1036, h786, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1035, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1044 | h1044
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1045 | h1045
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1046 | h1046
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1047 | h1047
                        · linarith only [h0, h1047, h786, h959, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1047, h210, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1044, h1046, h786, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1044, h1045, h786, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1044, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
