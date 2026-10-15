import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6122000 in
set_option maxHeartbeats 6122000 in
theorem r1l7_20_12_14_H_L_L_I_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                · linarith only [h0, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h3, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                · linarith only [h0, h11, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h11, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                · linarith only [h0, h15, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h15, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h18, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h18, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h21 | h21
            · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
              · linarith only [h21, h22, h3, h5, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                · linarith only [h0, h24, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h24, h3, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
              · linarith only [h27, h4, h5, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                · linarith only [h0, h29, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h29, h3, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h32 | h32
          · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
            · linarith only [h3, h33, h4, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h35 | h35
              · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
                · linarith only [h0, h36, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h3, h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h32, h35, h4, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h40 | h40
            · linarith only [h3, h4, h40, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
              · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
                · linarith only [h0, h43, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h2, h3, h32, h42, h43, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                · linarith only [h0, h46, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h3, h46, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h49 | h49
        · rcases m.htr 0 2 5 (by decide) (by decide) with h50 | h50
          · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
            · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
              · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                · linarith only [h0, h3, h53, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                  · linarith only [h1, h53, h55, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h49, h55, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                · linarith only [h0, h3, h58, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                  · linarith only [h1, h58, h60, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h49, h60, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h3, h49, h51, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h64 | h64
            · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
              · linarith only [h49, h50, h65, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                · linarith only [h0, h3, h67, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                  · linarith only [h1, h67, h69, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h49, h69, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h3, h49, h64, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h73 | h73
          · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
            · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                · linarith only [h0, h76, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                  · linarith only [h1, h49, h76, h78, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h1, h76, h80, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h73, h80, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h49, h73, h75, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h84 | h84
              · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
                · linarith only [h0, h3, h85, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
                  · linarith only [h1, h85, h87, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
                    · linarith only [h1, h85, h89, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h73, h89, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h3, h73, h74, h84, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h93 | h93
            · rcases m.htr 0 4 5 (by decide) (by decide) with h94 | h94
              · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                · linarith only [h0, h3, h95, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                  · linarith only [h0, h49, h97, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
                    · linarith only [h1, h73, h95, h99, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                      · linarith only [h1, h101, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h101, h93, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
                · linarith only [h0, h104, h3, h93, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                  · linarith only [h0, h106, h49, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                    · linarith only [h0, h108, h73, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                      · linarith only [h1, h110, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h104, h110, h93, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
              · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
                · linarith only [h0, h114, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h116 | h116
                  · linarith only [h1, h114, h116, h49, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                    · linarith only [h0, h118, h73, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h120 | h120
                      · linarith only [h1, h120, h93, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
                        · linarith only [h122, h2, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h113, h114, h120, h122, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h125 | h125
                · linarith only [h0, h125, h3, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                  · linarith only [h0, h127, h49, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                    · linarith only [h0, h129, h73, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                      · linarith only [h1, h131, h3, h93, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h133 | h133
                        · linarith only [h0, h113, h133, h2, h3, h93, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
                                · linarith only [h0, h113, h135, h138, h3, h93, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h137, h138, h3, h93, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                                · linarith only [h0, h137, h141, h49, hc12, hc34, hlam, hphi, ht23]
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
                                    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p143_1, u0elo1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h3, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h49, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h73, hlam, p143_0]
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
                                    linarith only [h125, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h127, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h129, hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    rcases p143_3 (m.d 0 2) (by simp) with h154 | h154
                                    · linarith only [h154, hlam, p143_0]
                                    · rcases p143_3 (m.d 1 2) (by simp) with h156 | h156
                                      · linarith only [h125, h156, hlam]
                                      · rcases p143_3 (m.d 2 3) (by simp) with h158 | h158
                                        · rcases p143_3 (m.d 2 4) (by simp) with h159 | h159
                                          · linarith only [h135, h159, hlam]
                                          · linarith only [h159, h49, hlam]
                                        · linarith only [h158, hlam, p143_0]
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
                                    linarith only [h135, h3, h93, hc02, hc23, hlam, hphi, p143_1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h0, h73, hc12, hc23, hlam, hphi, p143_1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h0, h137, hc12, hc45, hlam, hphi, ht23, ht34, p143_1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h137, hc12, hc45, hlam, hphi, ht23, ht34, p143_1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h135, hlam, p143_1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [hlam, p143_0]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h137, hlam, p143_1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    rcases p143_3 (m.d 0 2) (by simp) with h174 | h174
                                    · linarith only [h174, hlam, p143_0]
                                    · rcases p143_3 (m.d 1 2) (by simp) with h176 | h176
                                      · linarith only [h129, h176, hlam]
                                      · rcases p143_3 (m.d 2 3) (by simp) with h178 | h178
                                        · rcases p143_3 (m.d 2 4) (by simp) with h179 | h179
                                          · linarith only [h137, h179, hlam]
                                          · linarith only [h179, h49, hlam]
                                        · linarith only [h178, h3, hlam]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    rcases p143_3 (m.d 0 2) (by simp) with h183 | h183
                                    · linarith only [h183, h73, hlam]
                                    · linarith only [h0, h183, hlam]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h136, hlam, p143_1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [h0, h49, hc12, hc25, hlam, hphi, p143_1]
                                  · have p143_0 := h143c.1
                                    have p143_1 := h143c.2.1
                                    have p143_2 := h143c.2.2.1
                                    have p143_3 := h143c.2.2.2
                                    linarith only [hlam, p143_0]
                            · linarith only [h0, h135, h136, h3, h93, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h191 | h191
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h192 | h192
                                · linarith only [h0, h113, h135, h190, h192, h3, h93, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h125, h131, h135, h190, h191, h192, h2, hc12, hc24, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h135, h190, h191, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h196 | h196
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h197 | h197
                                · rcases h2bigk with h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p198_1, u0elo1]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h3, hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h49, hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h73, hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h0, hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h125, hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h127, hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h129, hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h190, hc02, hc35, hlam, hphi, ht23, p198_1]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h190, hc12, hc35, hlam, hphi, ht23, p198_1]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h135, hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h190, hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    rcases p198_3 (m.d 0 2) (by simp) with h214 | h214
                                    · linarith only [h214, hlam, p198_0]
                                    · rcases p198_3 (m.d 1 2) (by simp) with h216 | h216
                                      · linarith only [h127, h216, hlam]
                                      · rcases p198_3 (m.d 2 3) (by simp) with h218 | h218
                                        · linarith only [h135, h218, hlam]
                                        · linarith only [h218, h3, hlam]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    rcases p198_3 (m.d 0 2) (by simp) with h221 | h221
                                    · linarith only [h221, h49, hlam]
                                    · linarith only [h0, h221, hlam]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h0, h135, h3, hc12, hc34, hlam, hphi, ht23, p198_1]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h0, h135, h190, h3, hc12, hc34, hlam, hphi, ht23, p198_1]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    rcases p198_3 (m.d 0 2) (by simp) with h227 | h227
                                    · linarith only [h227, hlam, p198_0]
                                    · rcases p198_3 (m.d 1 2) (by simp) with h229 | h229
                                      · linarith only [h129, h229, hlam]
                                      · rcases p198_3 (m.d 2 3) (by simp) with h231 | h231
                                        · linarith only [h190, h231, hlam]
                                        · linarith only [h231, h3, hlam]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    rcases p198_3 (m.d 0 2) (by simp) with h234 | h234
                                    · linarith only [h234, h73, hlam]
                                    · linarith only [h0, h234, hlam]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h0, h3, hc12, hc25, hlam, hphi, p198_1]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [h196, hlam, p198_0]
                                  · have p198_0 := h198c.1
                                    have p198_1 := h198c.2.1
                                    have p198_2 := h198c.2.2.1
                                    have p198_3 := h198c.2.2.2
                                    linarith only [hlam, p198_0]
                                · linarith only [h135, h196, h197, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h241 | h241
                                · linarith only [h0, h135, h196, h241, h3, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h135, h241, h3, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h244 | h244
      · rcases m.htr 0 2 4 (by decide) (by decide) with h245 | h245
        · linarith only [h0, h2, h245, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h247 | h247
          · rcases m.htr 0 3 4 (by decide) (by decide) with h248 | h248
            · linarith only [h0, h2, h244, h248, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h250 | h250
              · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
                · linarith only [h0, h251, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h244, h251, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h2, h247, h250, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h255 | h255
            · linarith only [h1, h2, h255, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h257 | h257
              · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
                · linarith only [h0, h258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h2, h244, h258, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
                · linarith only [h0, h2, h257, h261, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h2, h244, h257, h261, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h264 | h264
        · linarith only [h1, h2, h244, h264, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h266 | h266
          · rcases m.htr 0 3 4 (by decide) (by decide) with h267 | h267
            · linarith only [h1, h2, h267, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h269 | h269
              · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
                · linarith only [h0, h244, h270, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h272 | h272
                  · linarith only [h0, h2, h264, h266, h272, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
                    · linarith only [h1, h2, h270, h274, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                    · linarith only [h266, h274, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1, h2, h244, h266, h269, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h278 | h278
            · linarith only [h1, h2, h278, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h280 | h280
              · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
                · linarith only [h0, h2, h281, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h283 | h283
                  · linarith only [h1, h2, h264, h281, h283, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h285 | h285
                    · linarith only [h0, h266, h285, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h287 | h287
                      · linarith only [h1, h2, h278, h287, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h290 | h290
                          · linarith only [h0, h2, h287, h290, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h294 | h294
                                · rcases h2bigk with h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p295_1, u0elo1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h244, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h264, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h266, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h0, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h281, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h283, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h285, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h290, hc02, hc34, hlam, hphi, ht23, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h290, hc12, hc34, hlam, hphi, ht23, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h290, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h0, h266, h290, hc12, hc34, hlam, hphi, ht23, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    rcases p295_3 (m.d 0 2) (by simp) with h311 | h311
                                    · linarith only [h311, hlam, p295_0]
                                    · rcases p295_3 (m.d 1 2) (by simp) with h313 | h313
                                      · linarith only [h283, h313, hlam]
                                      · rcases p295_3 (m.d 2 3) (by simp) with h315 | h315
                                        · linarith only [h290, h315, hlam]
                                        · linarith only [h244, h315, hlam]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    rcases p295_3 (m.d 0 2) (by simp) with h318 | h318
                                    · linarith only [h264, h318, hlam]
                                    · linarith only [h0, h318, hlam]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h0, h244, hc12, hc24, hlam, hphi, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h0, h266, h290, hc12, hc34, hlam, hphi, ht23, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h0, h290, h292, hc12, hc34, hlam, hphi, ht23, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h290, h292, hc12, hc34, hlam, hphi, ht23, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h292, hlam, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h293, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hlam, p295_0]
                                · linarith only [h280, h285, h290, h292, h294, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                              · linarith only [h2, h280, h283, h293, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h331 | h331
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                                · rcases h2bigk with h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p333_1, u0elo1]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h244, hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h264, hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h266, hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h0, hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h281, hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h283, hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h285, hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h292, hc02, hc35, hlam, hphi, ht23, p333_1]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h292, hc12, hc35, hlam, hphi, ht23, p333_1]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h290, hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h292, hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    rcases p333_3 (m.d 0 2) (by simp) with h349 | h349
                                    · linarith only [h349, hlam, p333_0]
                                    · rcases p333_3 (m.d 1 2) (by simp) with h351 | h351
                                      · linarith only [h283, h351, hlam]
                                      · rcases p333_3 (m.d 2 3) (by simp) with h353 | h353
                                        · linarith only [h290, h353, hlam]
                                        · linarith only [h244, h353, hlam]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    rcases p333_3 (m.d 0 2) (by simp) with h356 | h356
                                    · linarith only [h264, h356, hlam]
                                    · linarith only [h0, h356, hlam]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h0, h244, hc12, hc24, hlam, hphi, p333_1]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h0, h266, hc12, hc24, hlam, hphi, p333_1]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    rcases p333_3 (m.d 0 2) (by simp) with h362 | h362
                                    · linarith only [h362, hlam, p333_0]
                                    · rcases p333_3 (m.d 1 2) (by simp) with h364 | h364
                                      · linarith only [h285, h364, hlam]
                                      · rcases p333_3 (m.d 2 3) (by simp) with h366 | h366
                                        · linarith only [h292, h366, hlam]
                                        · linarith only [h244, h366, hlam]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    rcases p333_3 (m.d 0 2) (by simp) with h369 | h369
                                    · linarith only [h266, h369, hlam]
                                    · linarith only [h0, h369, hlam]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h0, h244, hc12, hc25, hlam, hphi, p333_1]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [h331, hlam, p333_0]
                                  · have p333_0 := h333c.1
                                    have p333_1 := h333c.2.1
                                    have p333_2 := h333c.2.2.1
                                    have p333_3 := h333c.2.2.2
                                    linarith only [hlam, p333_0]
                                · linarith only [h280, h290, h332, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                              · linarith only [h1, h2, h280, h281, h283, h331, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1, h2, h280, h281, h289, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h378 | h378
                · linarith only [h0, h244, h378, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h380 | h380
                  · linarith only [h0, h380, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h382 | h382
                    · linarith only [h1, h2, h266, h280, h378, h382, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h384 | h384
                      · linarith only [h1, h2, h278, h280, h384, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h386 | h386
                        · linarith only [h1, h2, h280, h378, h380, h386, hc12, hc24, hlam, hphi]
                        · linarith only [h1, h2, h378, h386, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h389 | h389
    · rcases m.htr 0 2 3 (by decide) (by decide) with h390 | h390
      · linarith only [h0, h1, h390, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h392 | h392
        · rcases m.htr 0 2 5 (by decide) (by decide) with h393 | h393
          · rcases m.htr 0 3 4 (by decide) (by decide) with h394 | h394
            · rcases m.htr 0 4 5 (by decide) (by decide) with h395 | h395
              · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
                · linarith only [h0, h1, h390, h392, h396, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h398 | h398
                  · linarith only [h0, h1, h398, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h392, h398, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h401 | h401
                · linarith only [h0, h1, h390, h401, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h403 | h403
                  · linarith only [h0, h1, h403, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h392, h403, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h1, h389, h394, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h407 | h407
            · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
              · linarith only [h392, h393, h408, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h410 | h410
                · linarith only [h0, h390, h410, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h412 | h412
                  · linarith only [h0, h1, h412, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h392, h412, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1, h392, h407, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h416 | h416
          · rcases m.htr 0 3 4 (by decide) (by decide) with h417 | h417
            · rcases m.htr 0 4 5 (by decide) (by decide) with h418 | h418
              · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                · linarith only [h0, h1, h390, h419, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h421 | h421
                  · linarith only [h0, h1, h392, h416, h421, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h423 | h423
                    · linarith only [h1, h389, h421, h423, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h416, h423, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h392, h416, h418, hlam]
            · linarith only [h1, h389, h417, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h428 | h428
            · rcases m.htr 0 4 5 (by decide) (by decide) with h429 | h429
              · rcases m.htr 1 2 3 (by decide) (by decide) with h430 | h430
                · linarith only [h0, h1, h390, h430, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h432 | h432
                  · linarith only [h0, h1, h432, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h434 | h434
                    · linarith only [h0, h416, h434, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h436 | h436
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h437 | h437
                        · linarith only [h1, h389, h437, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h1, h389, h429, h432, h437, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1, h436, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
                · linarith only [h0, h441, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h443 | h443
                  · linarith only [h0, h392, h443, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h445 | h445
                    · linarith only [h1, h389, h416, h429, h443, h445, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h448 | h448
                        · linarith only [h389, h429, h448, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h451 | h451
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h453 | h453
                                · linarith only [h389, h429, h447, h453, hlam]
                                · rcases h2bigk with h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p455_1, u0elo1]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h390, hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h392, hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h416, hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h0, hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h441, hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h443, hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h445, hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    rcases p455_3 (m.d 0 2) (by simp) with h466 | h466
                                    · linarith only [h466, hlam, p455_0]
                                    · rcases p455_3 (m.d 1 2) (by simp) with h468 | h468
                                      · linarith only [h441, h468, hlam]
                                      · rcases p455_3 (m.d 2 3) (by simp) with h470 | h470
                                        · rcases p455_3 (m.d 2 4) (by simp) with h471 | h471
                                          · linarith only [h450, h471, hlam]
                                          · linarith only [h392, h471, hlam]
                                        · linarith only [h470, hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    rcases p455_3 (m.d 0 2) (by simp) with h475 | h475
                                    · linarith only [h390, h475, hlam]
                                    · linarith only [h0, h475, hlam]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h392, h429, h452, hc02, hc23, hlam, hphi, p455_1]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h0, h392, h429, h452, hc12, hc23, hlam, hphi, p455_1]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    rcases p455_3 (m.d 0 2) (by simp) with h481 | h481
                                    · linarith only [h481, hlam, p455_0]
                                    · rcases p455_3 (m.d 1 2) (by simp) with h483 | h483
                                      · linarith only [h443, h483, hlam]
                                      · rcases p455_3 (m.d 2 3) (by simp) with h485 | h485
                                        · rcases p455_3 (m.d 2 4) (by simp) with h486 | h486
                                          · rcases p455_3 (m.d 2 5) (by simp) with h487 | h487
                                            · linarith only [h452, h487, hlam]
                                            · linarith only [h416, h487, hlam]
                                          · linarith only [h486, hlam, p455_0]
                                        · linarith only [h390, h485, hlam]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    rcases p455_3 (m.d 0 2) (by simp) with h492 | h492
                                    · linarith only [h392, h492, hlam]
                                    · linarith only [h0, h492, hlam]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h450, hlam, p455_1]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h0, h392, h429, h452, hc12, hc24, hlam, hphi, p455_1]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    rcases p455_3 (m.d 0 2) (by simp) with h498 | h498
                                    · linarith only [h498, hlam, p455_0]
                                    · rcases p455_3 (m.d 1 2) (by simp) with h500 | h500
                                      · linarith only [h445, h500, hlam]
                                      · rcases p455_3 (m.d 2 3) (by simp) with h502 | h502
                                        · rcases p455_3 (m.d 2 4) (by simp) with h503 | h503
                                          · rcases p455_3 (m.d 2 5) (by simp) with h504 | h504
                                            · rcases h4bigk with h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h443, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1, u0elo3]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h392, hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h1, h389, hc34, hlam, hphi, ht0b, ht45, ht5b, p505_1, u0elo2]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h429, hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h389, hlam, p505_1]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h443, hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h1, h389, hc34, hlam, hphi, ht0b, ht45, ht5b, p505_1, u0elo2]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h448, hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                rcases p505_3 (m.d 0 4) (by simp) with h516 | h516
                                                · linarith only [h392, h516, hlam]
                                                · rcases p505_3 (m.d 1 4) (by simp) with h518 | h518
                                                  · linarith only [h443, h518, hlam]
                                                  · rcases p505_3 (m.d 2 4) (by simp) with h520 | h520
                                                    · rcases p505_3 (m.d 3 4) (by simp) with h521 | h521
                                                      · linarith only [h450, h521, hlam]
                                                      · rcases p505_3 (m.d 4 5) (by simp) with h523 | h523
                                                        · linarith only [h452, h523, hlam]
                                                        · linarith only [h429, h523, hlam]
                                                    · linarith only [h392, h520, hlam]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                rcases p505_3 (m.d 0 4) (by simp) with h527 | h527
                                                · linarith only [h392, h527, hlam]
                                                · linarith only [h389, h527, hlam]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                rcases p505_3 (m.d 0 4) (by simp) with h531 | h531
                                                · linarith only [h392, h531, hlam]
                                                · linarith only [h428, h531, hlam]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h0, h392, h429, h450, hc12, hc23, hlam, hphi, p505_1]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h428, hlam, p505_1]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h447, hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h450, hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h453, hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h0, h392, h450, h452, hc12, hc23, hlam, hphi, p505_1]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h443, h450, h452, hc12, hc23, hlam, hphi, p505_1]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [h452, hlam, p505_0]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                rcases p505_3 (m.d 0 4) (by simp) with h543 | h543
                                                · linarith only [h429, h543, hlam]
                                                · linarith only [h428, h543, hlam]
                                              · have p505_0 := h505c.1
                                                have p505_1 := h505c.2.1
                                                have p505_2 := h505c.2.2.1
                                                have p505_3 := h505c.2.2.2
                                                linarith only [hlam, p505_0]
                                            · linarith only [h504, hlam, p455_0]
                                          · linarith only [h392, h503, hlam]
                                        · linarith only [h390, h502, hlam]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    rcases p455_3 (m.d 0 2) (by simp) with h550 | h550
                                    · linarith only [h416, h550, hlam]
                                    · linarith only [h0, h550, hlam]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h451, hlam, p455_1]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [h452, hlam, p455_0]
                                  · have p455_0 := h455c.1
                                    have p455_1 := h455c.2.1
                                    have p455_2 := h455c.2.2.1
                                    have p455_3 := h455c.2.2.2
                                    linarith only [hlam, p455_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h556 | h556
                                · linarith only [h0, h392, h452, h556, hc12, hc34, hlam, hphi, ht23]
                                · rcases h2bigk with h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p558_1, u0elo1]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h390, hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h392, hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h416, hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h0, hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h441, hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h443, hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h445, hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    rcases p558_3 (m.d 0 2) (by simp) with h569 | h569
                                    · linarith only [h569, hlam, p558_0]
                                    · rcases p558_3 (m.d 1 2) (by simp) with h571 | h571
                                      · linarith only [h441, h571, hlam]
                                      · rcases p558_3 (m.d 2 3) (by simp) with h573 | h573
                                        · rcases p558_3 (m.d 2 4) (by simp) with h574 | h574
                                          · linarith only [h450, h574, hlam]
                                          · linarith only [h392, h574, hlam]
                                        · linarith only [h573, hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    rcases p558_3 (m.d 0 2) (by simp) with h578 | h578
                                    · linarith only [h390, h578, hlam]
                                    · linarith only [h0, h578, hlam]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h392, hc02, hc23, hlam, hphi, p558_1]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h0, h416, hc12, hc23, hlam, hphi, p558_1]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h0, h452, hc12, hc45, hlam, hphi, ht23, ht34, p558_1]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h452, hc12, hc45, hlam, hphi, ht23, ht34, p558_1]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h450, hlam, p558_1]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [hlam, p558_0]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h452, hlam, p558_1]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    rcases p558_3 (m.d 0 2) (by simp) with h589 | h589
                                    · linarith only [h589, hlam, p558_0]
                                    · rcases p558_3 (m.d 1 2) (by simp) with h591 | h591
                                      · linarith only [h445, h591, hlam]
                                      · rcases p558_3 (m.d 2 3) (by simp) with h593 | h593
                                        · rcases p558_3 (m.d 2 4) (by simp) with h594 | h594
                                          · linarith only [h452, h594, hlam]
                                          · linarith only [h392, h594, hlam]
                                        · linarith only [h390, h593, hlam]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    rcases p558_3 (m.d 0 2) (by simp) with h598 | h598
                                    · linarith only [h416, h598, hlam]
                                    · linarith only [h0, h598, hlam]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h451, hlam, p558_1]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [h0, h392, hc12, hc25, hlam, hphi, p558_1]
                                  · have p558_0 := h558c.1
                                    have p558_1 := h558c.2.1
                                    have p558_2 := h558c.2.2.1
                                    have p558_3 := h558c.2.2.2
                                    linarith only [hlam, p558_0]
                            · linarith only [h1, h389, h441, h443, h451, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h389, h441, h447, h450, hlam]
                      · linarith only [h1, h389, h443, h447, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h389, h428, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h608 | h608
      · linarith only [h0, h1, h608, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h610 | h610
        · linarith only [h0, h389, h610, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h612 | h612
          · rcases m.htr 0 3 4 (by decide) (by decide) with h613 | h613
            · rcases m.htr 0 4 5 (by decide) (by decide) with h614 | h614
              · rcases m.htr 1 2 3 (by decide) (by decide) with h615 | h615
                · linarith only [h0, h608, h615, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h617 | h617
                  · linarith only [h0, h389, h610, h612, h613, h617, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h619 | h619
                    · linarith only [h0, h389, h613, h619, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h612, h619, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h389, h612, h614, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h623 | h623
              · rcases m.htr 1 2 3 (by decide) (by decide) with h624 | h624
                · linarith only [h0, h608, h624, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h626 | h626
                  · linarith only [h0, h1, h610, h612, h613, h626, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h628 | h628
                    · linarith only [h0, h1, h613, h628, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                    · linarith only [h612, h628, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1, h612, h613, h623, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h632 | h632
            · rcases m.htr 0 4 5 (by decide) (by decide) with h633 | h633
              · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
                · linarith only [h0, h608, h634, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
                  · linarith only [h0, h389, h610, h636, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h638 | h638
                    · linarith only [h0, h389, h612, h632, h638, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h640 | h640
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h641 | h641
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h642 | h642
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h643 | h643
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h644 | h644
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h645 | h645
                                · linarith only [h632, h645, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h632, h633, h645, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · linarith only [h389, h632, h633, h636, h644, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h0, h389, h634, h640, h643, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h389, h634, h640, h642, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h389, h632, h633, h641, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h632, h640, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h653 | h653
                · linarith only [h0, h608, h653, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h655 | h655
                  · linarith only [h0, h389, h633, h655, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h657 | h657
                    · linarith only [h0, h389, h612, h633, h657, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h659 | h659
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h660 | h660
                        · linarith only [h0, h389, h633, h653, h659, h660, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h389, h660, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h1, h659, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h664 | h664
              · rcases m.htr 1 2 3 (by decide) (by decide) with h665 | h665
                · linarith only [h0, h665, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h667 | h667
                  · linarith only [h0, h1, h632, h667, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h669 | h669
                    · linarith only [h0, h1, h612, h632, h669, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h671 | h671
                      · linarith only [h0, h1, h632, h665, h671, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h671, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h674 | h674
                · linarith only [h0, h1, h632, h664, h674, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h676 | h676
                  · linarith only [h0, h1, h632, h664, h676, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h678 | h678
                    · linarith only [h0, h1, h612, h632, h664, h678, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h680 | h680
                      · linarith only [h0, h1, h632, h674, h680, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h680, hc12, hc34, hlam, hphi, ht23]

end R2N4
