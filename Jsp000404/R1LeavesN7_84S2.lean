import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_25_L_0_L_I_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
          · linarith only [h1, h3, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
            · linarith only [h0, h3, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
              · linarith only [h1, h3, h7, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                · linarith only [h1, h11, h3, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h1, h13, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h13, h15, h2, h3, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h17, h2, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h13, h15, h2, h20, h3, h7, hc12, hc23, hlam, hphi]
                          · linarith only [h13, h19, h20, h7, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                          · linarith only [h13, h19, h2, h23, h3, h7, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht5b, u1elo4, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                            · linarith only [h13, h17, h2, h25, h3, h7, hc12, hc24, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                              · linarith only [h19, h25, h27, h7, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h19, h27, h7, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h30 | h30
        · linarith only [h2, h30, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h32 | h32
          · linarith only [h1, h2, h32, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
            · linarith only [h0, h2, h34, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
              · linarith only [h1, h2, h34, h36, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
                · linarith only [h1, h2, h34, h38, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                  · linarith only [h1, h2, h40, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                    · linarith only [h1, h2, h32, h42, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h44, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                      · linarith only [h1, h2, h34, h44, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h47 | h47
      · rcases m.htr 0 1 5 (by decide) (by decide) with h48 | h48
        · linarith only [h1, h48, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h50 | h50
          · linarith only [h1, h50, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
            · linarith only [h0, h1, h52, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
              · linarith only [h0, h1, h54, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                · linarith only [h1, h47, h54, h56, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h59, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · linarith only [h1, h47, h54, h59, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h47, h54, h58, hc12, hc34, hlam, hphi, ht23]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h63 | h63
        · linarith only [h1, h63, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h65 | h65
          · linarith only [h1, h65, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
            · linarith only [h0, h1, h67, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
              · linarith only [h0, h1, h69, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                · linarith only [h0, h1, h71, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h74, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · linarith only [h0, h47, h73, h74, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1, h73, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h78 | h78
    · rcases m.htr 0 1 4 (by decide) (by decide) with h79 | h79
      · rcases m.htr 0 1 5 (by decide) (by decide) with h80 | h80
        · linarith only [h0, h80, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h82 | h82
          · linarith only [h0, h78, h82, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
            · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
              · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                · linarith only [h86, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                  · linarith only [h0, h78, h86, h88, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
                    · linarith only [h0, h79, h82, h86, h88, h90, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                      · linarith only [h0, h79, h86, h92, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                        · linarith only [h84, h88, h94, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                          · linarith only [h0, h79, h84, h86, h88, h90, h96, hlam]
                          · linarith only [h0, h79, h86, h88, h96, hc13, hc35, hlam, hphi]
              · linarith only [h0, h79, h85, hlam]
            · linarith only [h0, h78, h84, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h101 | h101
        · linarith only [h0, h101, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h103 | h103
          · linarith only [h0, h103, h78, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
            · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
              · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                · linarith only [h107, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
                  · linarith only [h106, h107, h109, h78, h79, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h111 | h111
                    · linarith only [h103, h106, h107, h111, h78, h79, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                      · linarith only [h106, h107, h113, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h113, h78, h79, hc13, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                · linarith only [h116, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                  · linarith only [h0, h106, h118, h78, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h120 | h120
                    · linarith only [h0, h106, h120, h78, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
                      · linarith only [h122, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                      · linarith only [h0, h105, h106, h122, h78, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h105, h78, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h126 | h126
      · rcases m.htr 0 1 5 (by decide) (by decide) with h127 | h127
        · linarith only [h0, h127, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h129 | h129
          · linarith only [h129, h78, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h131 | h131
            · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
              · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                · linarith only [h133, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                    · linarith only [h131, h133, h136, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                      · linarith only [h126, h131, h133, h138, h78, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h141 | h141
                          · linarith only [h126, h131, h132, h133, h136, h140, h141, h78, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h143 | h143
                            · linarith only [h126, h132, h133, h138, h143, h78, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · linarith only [h126, h131, h133, h143, h78, hc14, hc45, hlam, hphi]
                        · linarith only [h135, h136, h140, hc23, hc35, hlam, hphi]
                  · linarith only [h126, h135, h78, hlam]
              · linarith only [h126, h131, h132, h78, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
              · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                · linarith only [h150, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                    · linarith only [h153, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                      · linarith only [h0, h126, h131, h153, h155, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                          · linarith only [h0, h131, h153, h158, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h126, h131, h149, h157, h158, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h126, h131, h149, h157, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h126, h131, h152, hlam]
              · linarith only [h0, h126, h149, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h164 | h164
        · linarith only [h0, h164, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
          · linarith only [h166, h78, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
            · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
              · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                · linarith only [h170, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h168, h170, h173, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                      · linarith only [h168, h170, h172, h175, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                          · linarith only [h126, h168, h170, h172, h173, h178, hc01, hc25, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                            · linarith only [h126, h168, h170, h175, h177, h178, h180, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h168, h170, h177, h180, hc34, hc45, hlam, hphi]
                        · linarith only [h172, h173, h177, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                    · linarith only [h184, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h186 | h186
                      · linarith only [h169, h170, h186, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
                        · linarith only [h172, h188, h78, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
                          · linarith only [h184, h190, h78, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                            · linarith only [h169, h170, h190, h192, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h194 | h194
                              · linarith only [h169, h170, h188, h192, h194, hc23, hc34, hlam, hphi]
                              · linarith only [h172, h194, h78, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                · linarith only [h197, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h199 | h199
                  · linarith only [h168, h169, h199, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h168, h201, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                      · linarith only [h203, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                        · linarith only [h199, h205, h78, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h207 | h207
                          · linarith only [h168, h169, h201, h203, h207, h78, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                            · linarith only [h168, h169, h203, h205, h209, hc23, hc34, hlam, hphi]
                            · linarith only [h168, h169, h209, h78, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h212 | h212
              · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                · linarith only [h213, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h216 | h216
                    · linarith only [h216, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h218 | h218
                      · linarith only [h168, h212, h216, h218, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h221 | h221
                          · linarith only [h0, h168, h216, h221, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h126, h168, h212, h221, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h126, h168, h212, h220, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h168, h212, h215, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
                · linarith only [h226, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                    · linarith only [h229, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                      · linarith only [h228, h229, h231, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h234 | h234
                          · linarith only [h0, h212, h228, h229, h234, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h168, h234, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h168, h228, h233, hc01, hlam, hphi, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h238 | h238
                    · linarith only [h238, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h240 | h240
                      · linarith only [h240, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
                        · linarith only [h228, h242, h78, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h168, h242, hc01, hc34, hlam, hphi, ht12, ht23]

theorem r1l7_11_12_25_L_R_L_I_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                              · linarith only [h13, h14, hc34, hlam, hphi, ht45, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h10, h13, h17, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                                · linarith only [h0, h19, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                                  · linarith only [h0, h10, h13, h19, h21, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h13, h21, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h12, h6, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo0]
                        · linarith only [h11, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                            · linarith only [h10, h26, h28, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                              · linarith only [h0, h30, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                              · linarith only [h10, h26, h30, hc23, hc34, hlam, hphi]
                          · linarith only [h10, h26, h27, hlam, hphi, u5ehi8, u5elo4]
                        · linarith only [h26, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                    · linarith only [h8, h9, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                    · linarith only [h0, h36, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                    · linarith only [h36, h7, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
                    · linarith only [h0, h3, h40, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                    · linarith only [h39, h40, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                    · linarith only [h0, h3, h43, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                    · linarith only [h43, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                          · linarith only [h2, h51, h6, hlam]
                          · linarith only [h51, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                        · linarith only [h49, h50, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h55 | h55
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
                          · linarith only [h2, h56, h6, hlam]
                          · linarith only [h56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                        · linarith only [h55, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                    · linarith only [h48, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                  · linarith only [h4, h47, h6, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                    · linarith only [h0, h3, h46, h63, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                    · linarith only [h62, h63, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h4, h6, h62, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo4]
            · linarith only [h3, h5, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h68 | h68
            · rcases m.htr 0 4 5 (by decide) (by decide) with h69 | h69
              · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
                · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
                  · linarith only [h0, h4, h68, h71, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h74 | h74
                      · linarith only [h70, h71, h74, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h76 | h76
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h77 | h77
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                            · linarith only [h74, h76, h78, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                              · linarith only [h0, h70, h80, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                              · linarith only [h1, h3, h4, h76, h78, h80, hc23, hc34, hlam, hphi]
                          · linarith only [h77, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                        · linarith only [h76, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                    · linarith only [h73, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                · linarith only [h3, h4, h70, hc24, hlam, hphi, ht12, u1ehi1]
              · linarith only [h3, h4, h69, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h1, h3, h68, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h89 | h89
          · rcases m.htr 0 2 5 (by decide) (by decide) with h90 | h90
            · rcases m.htr 0 4 5 (by decide) (by decide) with h91 | h91
              · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                · linarith only [h3, h89, h91, h92, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h97 | h97
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h100 | h100
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h101 | h101
                                · linarith only [h0, h101, h3, h94, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h103 | h103
                                  · linarith only [h101, h103, h99, hlam]
                                  · rcases h2bigk with h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h3, hc12, hc23, hlam, hphi, p105_1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h3, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      rcases p105_3 (m.d 0 2) (by simp) with h109 | h109
                                      · rcases p105_3 (m.d 1 2) (by simp) with h110 | h110
                                        · linarith only [h0, h110, hlam]
                                        · linarith only [h110, h94, hlam]
                                      · linarith only [h109, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h100, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p105_1, u5ehi8]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, hlam, p105_1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h92, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      rcases p105_3 (m.d 0 2) (by simp) with h118 | h118
                                      · rcases p105_3 (m.d 1 2) (by simp) with h119 | h119
                                        · rcases p105_3 (m.d 2 3) (by simp) with h120 | h120
                                          · rcases p105_3 (m.d 2 4) (by simp) with h121 | h121
                                            · linarith only [h121, hlam, p105_0]
                                            · rcases p105_3 (m.d 2 5) (by simp) with h123 | h123
                                              · linarith only [h123, h95, hlam]
                                              · linarith only [h101, h123, hlam]
                                          · linarith only [h120, h99, hlam]
                                        · linarith only [h119, hlam, p105_0]
                                      · linarith only [h118, h89, hlam]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, h100, hc01, hlam, hphi, ht0b, ht5b, p105_1, u5ehi8]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht12, p105_1, u1ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht12, p105_1, u1ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, h101, h3, h94, h98, hlam, p105_2]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      rcases p105_3 (m.d 0 2) (by simp) with h134 | h134
                                      · linarith only [h134, h3, hlam]
                                      · linarith only [h134, h90, hlam]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h89, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h94, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h99, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h101, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h90, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h95, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h100, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h99, hc34, hlam, hphi, ht45, p105_1, u5elo2]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                              · linarith only [h0, h100, h3, h95, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                            · linarith only [h0, h3, h94, h98, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                          · linarith only [h98, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                        · linarith only [h96, h97, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h92, h94, h96, hlam]
                    · linarith only [h95, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                  · linarith only [h3, h89, h94, hc23, hlam, hphi, ht12, u1ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
                · linarith only [h154, h2, h3, h90, h91, hc12, hlam, hphi, u1ehi4, u5ehi7, u5elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h157 | h157
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h159 | h159
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h160 | h160
                          · linarith only [h0, h156, h160, h2, h3, h91, hc23, hlam, hphi, ht12, u1ehi4]
                          · linarith only [h160, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                        · linarith only [h158, h159, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h154, h156, h158, hlam]
                    · linarith only [h157, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                  · linarith only [h156, h89, h91, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
            · linarith only [h89, h90, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h168 | h168
            · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
              · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                · linarith only [h168, h170, h3, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
                  · linarith only [h0, h172, h89, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h175 | h175
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h176 | h176
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h181 | h181
                                  · linarith only [h1, h175, h181, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                  · rcases h2bigk with h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h174, h180, h181, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p183_1]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h3, hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h89, hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h178, h180, h181, h89, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p183_1]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h0, hlam, p183_1]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h170, hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h172, hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h0, h180, h181, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p183_1]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht12, p183_1, u1ehi1]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht12, p183_1, u1ehi1]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h168, h180, h181, h89, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p183_1]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      rcases p183_3 (m.d 0 2) (by simp) with h198 | h198
                                      · linarith only [h198, h3, hlam]
                                      · linarith only [h168, h198, hlam]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h0, h174, h180, h181, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p183_1]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h174, h180, h181, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p183_1]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h178, hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      rcases p183_3 (m.d 0 2) (by simp) with h205 | h205
                                      · linarith only [h205, h89, hlam]
                                      · linarith only [h168, h205, hlam]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h168, hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h174, hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h179, hlam, p183_0]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [h180, hlam, p183_1]
                                    · have p183_0 := h183c.1
                                      have p183_1 := h183c.2.1
                                      have p183_2 := h183c.2.2.1
                                      have p183_3 := h183c.2.2.2
                                      linarith only [hlam, p183_0]
                                · linarith only [h0, h174, h180, h89, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                              · linarith only [h0, h174, h179, h3, hlam, hphi, u5ehi7, u5elo3]
                            · linarith only [h0, h174, h178, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                          · linarith only [h177, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                        · linarith only [h175, h176, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h218 | h218
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
                            · linarith only [h170, h174, h175, h220, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                            · linarith only [h0, h174, h220, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                          · linarith only [h219, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                        · linarith only [h170, h174, h218, hlam, hphi, u5ehi7, u5elo3]
                    · linarith only [h174, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
              · linarith only [h168, h169, h89, hlam, hphi, u5ehi7, u5elo4]
            · linarith only [h0, h168, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h230 | h230
    · linarith only [h0, h230, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h232 | h232
      · linarith only [h0, h232, hc12, hlam, hphi, u1ehi4]
      · linarith only [h232, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_11_13_25_L_0_L_0_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · rcases h5bigk with h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc15, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hc35, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc35, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc45, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc05, hlam, hphi, p4_1, u5elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hc35, hlam, hphi, p4_1, u5elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc35, hlam, hphi, p4_1, u5elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc45, hlam, hphi, p4_1, u5elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc05, hlam, hphi, p4_1, u5elo2]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, hlam, p4_1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc35, hlam, hphi, p4_1, u5elo2]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p4_1, u1elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc05, hlam, hphi, p4_1, u5elo3]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4_1, u3elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc05, hlam, hphi, p4_1, u5elo4]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht5b, p4_1, u1elo3]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht5b, p4_1, u1elo3]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
        · linarith only [h1, h3, hc23, hlam, hphi, u3elo1]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
        · rcases h5bigk with h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hlam, p32_0]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hc15, hlam, hphi, p32_1, u5elo0]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hc25, hlam, hphi, p32_1, u5elo0]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hc35, hlam, hphi, p32_1, u5elo0]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hc45, hlam, hphi, p32_1, u5elo0]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hc05, hlam, hphi, p32_1, u5elo1]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hlam, p32_0]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hc25, hlam, hphi, p32_1, u5elo1]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hc35, hlam, hphi, p32_1, u5elo1]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [h2, hlam, p32_1]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hc05, hlam, hphi, p32_1, u5elo2]
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
            linarith only [hc35, hlam, hphi, p32_1, u5elo2]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [h0, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p32_1, u1elo1]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [h31, hc05, hlam, hphi, p32_1, u5elo2]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [h1, hlam, p32_0]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [h31, hlam, p32_0]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hlam, p32_0]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [h1, h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p32_1, u3elo1]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hc05, hlam, hphi, p32_1, u5elo4]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [h2, hc14, hlam, hphi, ht45, p32_1, u5elo4]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [h31, hc35, hlam, hphi, p32_1, u5elo4]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hc35, hlam, hphi, p32_1, u5elo4]
          · have p32_0 := h32c.1
            have p32_1 := h32c.2.1
            have p32_2 := h32c.2.2.1
            have p32_3 := h32c.2.2.2
            linarith only [hlam, p32_0]
        · linarith only [h1, h31, hc23, hlam, hphi, u3elo1]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
      · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
        · linarith only [h1, h60, hc13, hlam, hphi, u3elo2]
        · rcases h5bigk with h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hlam, p62_0]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h0, h60, hc23, hlam, hphi, ht34, ht45, p62_1, u5elo0]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h60, hc23, hlam, hphi, ht34, ht45, p62_1, u5elo0]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h1, hc13, hlam, hphi, ht34, ht45, p62_1, u5elo0]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hc45, hlam, hphi, p62_1, u5elo0]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hc05, hlam, hphi, p62_1, u5elo1]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hlam, p62_0]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h60, hc23, hlam, hphi, ht34, ht45, p62_1, u5elo1]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h1, hlam, p62_1]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h1, hc45, hlam, hphi, p62_1, u5elo3]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hc05, hlam, hphi, p62_1, u5elo2]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h0, hlam, p62_1]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hlam, p62_0]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h60, hlam, p62_1]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p62_1, u1elo1]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hc05, hlam, hphi, p62_1, u5elo3]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hc15, hlam, hphi, p62_1, u5elo3]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hc25, hlam, hphi, p62_1, u5elo3]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hlam, p62_0]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hc45, hlam, hphi, p62_1, u5elo3]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hc05, hlam, hphi, p62_1, u5elo4]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h59, hlam, p62_0]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h59, h60, hc23, hlam, hphi, ht34, ht45, p62_1, u5elo1]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [h1, h59, hlam, p62_1]
          · have p62_0 := h62c.1
            have p62_1 := h62c.2.1
            have p62_2 := h62c.2.2.1
            have p62_3 := h62c.2.2.2
            linarith only [hlam, p62_0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
        · linarith only [h1, h88, hc13, hlam, hphi, u3elo2]
        · rcases h5bigk with h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hlam, p90_0]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hc15, hlam, hphi, p90_1, u5elo0]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h88, hc23, hlam, hphi, ht34, ht45, p90_1, u5elo0]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h1, hc13, hlam, hphi, ht34, ht45, p90_1, u5elo0]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h59, hc14, hlam, hphi, ht45, p90_1, u5elo0]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hc05, hlam, hphi, p90_1, u5elo1]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hlam, p90_0]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h88, hc23, hlam, hphi, ht34, ht45, p90_1, u5elo1]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h1, hlam, p90_1]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h59, hlam, p90_1]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hc05, hlam, hphi, p90_1, u5elo2]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h0, hlam, p90_1]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hlam, p90_0]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h88, hlam, p90_1]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h0, h59, hc15, hlam, hphi, ht01, ht0b, ht5b, p90_1, u1elo1]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hc05, hlam, hphi, p90_1, u5elo3]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hc15, hlam, hphi, p90_1, u5elo3]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hc25, hlam, hphi, p90_1, u5elo3]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hlam, p90_0]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h59, hc14, hlam, hphi, ht45, p90_1, u5elo3]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hc05, hlam, hphi, p90_1, u5elo4]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h0, h88, hc23, hlam, hphi, ht34, ht45, p90_1, u5elo4]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [h88, hc23, hlam, hphi, ht34, ht45, p90_1, u5elo4]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hc35, hlam, hphi, p90_1, u5elo4]
          · have p90_0 := h90c.1
            have p90_1 := h90c.2.1
            have p90_2 := h90c.2.2.1
            have p90_3 := h90c.2.2.2
            linarith only [hlam, p90_0]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
    · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
      · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
        · rcases h5bigk with h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hlam, p119_0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hc15, hlam, hphi, p119_1, u5elo0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p119_1, u5elo0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hc35, hlam, hphi, p119_1, u5elo0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hc45, hlam, hphi, p119_1, u5elo0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hc05, hlam, hphi, p119_1, u5elo1]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hlam, p119_0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [h0, hlam, p119_0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hc35, hlam, hphi, p119_1, u5elo1]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p119_1, u5elo2]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hc05, hlam, hphi, p119_1, u5elo2]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hc15, hlam, hphi, p119_1, u5elo2]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hlam, p119_0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hc35, hlam, hphi, p119_1, u5elo2]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hc45, hlam, hphi, p119_1, u5elo2]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [h116, hc05, hlam, hphi, ht01, ht0b, ht5b, p119_1, u1elo2]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [h116, hlam, p119_0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [h118, hlam, p119_0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hlam, p119_0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [h116, hc45, hlam, hphi, p119_1, u5elo1]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hc05, hlam, hphi, p119_1, u5elo4]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [h117, hlam, p119_0]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [h0, h117, hc15, hlam, hphi, ht01, ht0b, ht5b, p119_1, u1elo3]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [h117, hc35, hlam, hphi, p119_1, u5elo1]
          · have p119_0 := h119c.1
            have p119_1 := h119c.2.1
            have p119_2 := h119c.2.2.1
            have p119_3 := h119c.2.2.2
            linarith only [hlam, p119_0]
        · linarith only [h116, h118, hc23, hlam, hphi, u3elo1]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
        · rcases h5bigk with h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hlam, p147_0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc15, hlam, hphi, p147_1, u5elo0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc25, hlam, hphi, p147_1, u5elo0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc35, hlam, hphi, p147_1, u5elo0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [h117, hc14, hlam, hphi, ht45, p147_1, u5elo0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc05, hlam, hphi, p147_1, u5elo1]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hlam, p147_0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [h0, hlam, p147_0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc35, hlam, hphi, p147_1, u5elo1]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [h117, hlam, p147_1]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc05, hlam, hphi, p147_1, u5elo2]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc15, hlam, hphi, p147_1, u5elo2]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hlam, p147_0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc35, hlam, hphi, p147_1, u5elo2]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [h117, hc14, hlam, hphi, ht45, p147_1, u5elo2]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc05, hlam, hphi, p147_1, u5elo3]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [h116, hlam, p147_0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [h146, hlam, p147_0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hlam, p147_0]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [h116, h117, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p147_1, u1elo4]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc05, hlam, hphi, p147_1, u5elo4]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc15, hlam, hphi, p147_1, u5elo4]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc25, hlam, hphi, p147_1, u5elo4]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hc35, hlam, hphi, p147_1, u5elo4]
          · have p147_0 := h147c.1
            have p147_1 := h147c.2.1
            have p147_2 := h147c.2.2.1
            have p147_3 := h147c.2.2.2
            linarith only [hlam, p147_0]
        · linarith only [h116, h146, hc23, hlam, hphi, u3elo1]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h174 | h174
      · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
        · linarith only [h116, h175, hc13, hlam, hphi, u3elo2]
        · rcases h5bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hlam, p177_0]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p177_1, u5elo0]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p177_1, u5elo0]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h0, h175, hc12, hlam, hphi, ht23, ht34, ht45, p177_1, u5elo0]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hc45, hlam, hphi, p177_1, u5elo0]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hc05, hlam, hphi, p177_1, u5elo1]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hlam, p177_0]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h0, hlam, p177_0]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h116, hlam, p177_1]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hc45, hlam, hphi, p177_1, u5elo1]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hc05, hlam, hphi, p177_1, u5elo2]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hc15, hlam, hphi, p177_1, u5elo2]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hlam, p177_0]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h175, hlam, p177_1]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h175, hc45, hlam, hphi, p177_1, u5elo3]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hc05, hlam, hphi, p177_1, u5elo3]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p177_1, u5elo3]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hc25, hlam, hphi, p177_1, u5elo3]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hlam, p177_0]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hc45, hlam, hphi, p177_1, u5elo3]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hc05, hlam, hphi, p177_1, u5elo4]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h174, hlam, p177_0]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h0, h174, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p177_1, u1elo4]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [h0, h174, h175, hlam, p177_1]
          · have p177_0 := h177c.1
            have p177_1 := h177c.2.1
            have p177_2 := h177c.2.2.1
            have p177_3 := h177c.2.2.2
            linarith only [hlam, p177_0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
        · linarith only [h116, h203, hc13, hlam, hphi, u3elo2]
        · rcases h5bigk with h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hlam, p205_0]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hc15, hlam, hphi, p205_1, u5elo0]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hc25, hlam, hphi, p205_1, u5elo0]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h0, h203, hc12, hlam, hphi, ht23, ht34, ht45, p205_1, u5elo0]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h174, hc14, hlam, hphi, ht45, p205_1, u5elo0]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hc05, hlam, hphi, p205_1, u5elo1]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hlam, p205_0]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h0, hlam, p205_0]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h116, hlam, p205_1]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h174, hlam, p205_1]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hc05, hlam, hphi, p205_1, u5elo2]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hc15, hlam, hphi, p205_1, u5elo2]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hlam, p205_0]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h203, hlam, p205_1]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h174, h203, hc14, hlam, hphi, ht45, p205_1, u5elo3]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hc05, hlam, hphi, p205_1, u5elo3]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p205_1, u5elo3]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hc25, hlam, hphi, p205_1, u5elo3]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hlam, p205_0]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h174, hc14, hlam, hphi, ht45, p205_1, u5elo3]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hc05, hlam, hphi, p205_1, u5elo4]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p205_1, u5elo4]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p205_1, u5elo4]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hc35, hlam, hphi, p205_1, u5elo4]
          · have p205_0 := h205c.1
            have p205_1 := h205c.2.1
            have p205_2 := h205c.2.2.1
            have p205_3 := h205c.2.2.2
            linarith only [hlam, p205_0]

end R2N4
