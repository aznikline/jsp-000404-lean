import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3010000 in
set_option maxHeartbeats 3010000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, h4, h8, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                      · linarith only [h0, h12, h4, h8, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h14, h4, h8, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · linarith only [h0, h14, h4, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                  · linarith only [h0, h17, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                    · linarith only [h0, h17, h19, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h17, h21, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                        · linarith only [h1, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h0, h23, h4, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                  · linarith only [h0, h27, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                    · linarith only [h0, h29, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                      · linarith only [h0, h27, h31, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                        · linarith only [h1, h33, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                          · linarith only [h0, h29, h33, h35, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                            · linarith only [h0, h29, h37, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h26, h33, h37, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
                  · linarith only [h0, h40, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                    · linarith only [h0, h42, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h0, h4, h40, h44, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                        · linarith only [h1, h46, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                          · linarith only [h1, h48, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                            · linarith only [h0, h26, h42, h5, h50, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                              · linarith only [h4, h52, h6, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                                · linarith only [h26, h5, h54, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                                  · linarith only [h26, h4, h40, h56, h6, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h4, h40, h56, h6, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h59 | h59
              · linarith only [h4, h5, h59, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
                · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
                  · linarith only [h0, h62, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h4, h5, h62, hc12, hc24, hlam, hphi]
                · linarith only [h4, h5, h61, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h66 | h66
            · rcases m.htr 0 3 4 (by decide) (by decide) with h67 | h67
              · rcases m.htr 0 4 5 (by decide) (by decide) with h68 | h68
                · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                  · linarith only [h4, h66, h68, h69, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
                    · linarith only [h0, h71, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                    · linarith only [h4, h66, h71, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
                  · linarith only [h4, h66, h74, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h76 | h76
                    · linarith only [h1, h74, h76, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                    · linarith only [h4, h66, h76, hc12, hc23, hlam, hphi]
              · linarith only [h4, h66, h67, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h80 | h80
              · rcases m.htr 0 4 5 (by decide) (by decide) with h81 | h81
                · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
                  · linarith only [h0, h82, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
                    · linarith only [h1, h66, h82, h84, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                        · linarith only [h1, h87, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · linarith only [h80, h87, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                        · linarith only [h1, h90, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1, h80, h90, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
                  · linarith only [h0, h4, h80, h93, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                    · linarith only [h1, h66, h93, h95, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                        · linarith only [h1, h98, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h80, h98, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                        · linarith only [h1, h101, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1, h101, h80, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h104 | h104
                · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                  · linarith only [h0, h105, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                    · linarith only [h0, h107, h66, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                        · linarith only [h1, h110, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
                          · linarith only [h110, h112, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                          · linarith only [h105, h109, h112, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                        · linarith only [h1, h115, h80, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h117 | h117
                          · linarith only [h1, h117, h80, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                            · linarith only [h119, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h104, h115, h119, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                  · linarith only [h0, h122, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                    · linarith only [h0, h124, h66, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
                        · linarith only [h1, h127, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                          · linarith only [h127, h129, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                          · linarith only [h122, h126, h129, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                        · linarith only [h1, h132, h4, h80, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                          · linarith only [h1, h134, h80, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                            · linarith only [h104, h136, h2, h80, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h140 | h140
                                  · linarith only [h1, h104, h140, h80, hc34, hlam, hphi, u3ehi1]
                                  · linarith only [h1, h138, h139, h140, h80, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                · linarith only [h1, h138, h139, h80, hc45, hlam, hphi, ht34, u3ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                                · linarith only [h1, h104, h138, h144, h80, hc34, hlam, hphi, u3ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h146 | h146
                                  · linarith only [h0, h138, h144, h146, h4, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h1, h146, h80, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h149 | h149
          · rcases m.htr 0 2 4 (by decide) (by decide) with h150 | h150
            · rcases m.htr 0 3 4 (by decide) (by decide) with h151 | h151
              · rcases m.htr 0 4 5 (by decide) (by decide) with h152 | h152
                · linarith only [h152, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
                  · linarith only [h0, h154, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                    · linarith only [h0, h156, h3, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h158 | h158
                      · linarith only [h0, h149, h154, h158, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                      · linarith only [h0, h149, h154, h158, h3, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h161 | h161
                · linarith only [h161, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
                  · linarith only [h0, h163, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h165 | h165
                    · linarith only [h149, h163, h165, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                      · linarith only [h0, h149, h163, h167, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                      · linarith only [h0, h149, h163, h167, h3, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h170 | h170
              · linarith only [h149, h150, h170, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h172 | h172
                · linarith only [h172, h2, h3, hlam]
                · linarith only [h149, h150, h172, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h175 | h175
            · rcases m.htr 0 3 4 (by decide) (by decide) with h176 | h176
              · rcases m.htr 0 4 5 (by decide) (by decide) with h177 | h177
                · linarith only [h0, h175, h177, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                  · linarith only [h149, h175, h179, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                    · linarith only [h1, h179, h181, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                    · linarith only [h149, h175, h181, hc12, hc23, hlam, hphi]
              · linarith only [h149, h175, h176, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h185 | h185
              · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
                · linarith only [h1, h185, h186, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
                  · linarith only [h0, h188, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
                    · linarith only [h1, h175, h188, h190, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h192 | h192
                      · linarith only [h0, h1, h192, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h194 | h194
                        · linarith only [h1, h192, h194, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h185, h194, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h197 | h197
                · linarith only [h197, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
                  · linarith only [h0, h149, h199, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
                    · linarith only [h0, h175, h185, h201, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
                      · linarith only [h0, h203, h3, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h205 | h205
                        · linarith only [h1, h203, h205, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h207 | h207
                          · linarith only [h2, h203, h205, h207, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h2, h205, h207, h3, hc35, hlam, hphi, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h210 | h210
        · rcases m.htr 0 2 3 (by decide) (by decide) with h211 | h211
          · rcases m.htr 0 2 4 (by decide) (by decide) with h212 | h212
            · linarith only [h0, h2, h212, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h214 | h214
              · linarith only [h0, h2, h211, h214, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
                · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                  · linarith only [h0, h2, h217, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                  · linarith only [h211, h212, h217, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h216, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h221 | h221
            · linarith only [h1, h2, h211, h221, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h223 | h223
              · linarith only [h1, h2, h223, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h225 | h225
                · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
                  · linarith only [h0, h211, h226, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h228 | h228
                    · linarith only [h0, h1, h2, h221, h228, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h230 | h230
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h231 | h231
                        · linarith only [h1, h2, h211, h223, h228, h231, hc02, hc24, hlam, hphi]
                        · linarith only [h1, h2, h231, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                        · linarith only [h1, h2, h228, h234, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · linarith only [h1, h2, h234, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h2, h225, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h238 | h238
          · rcases m.htr 0 2 4 (by decide) (by decide) with h239 | h239
            · linarith only [h0, h2, h239, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h241 | h241
              · linarith only [h0, h2, h238, h241, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h243 | h243
                · rcases m.htr 1 2 3 (by decide) (by decide) with h244 | h244
                  · linarith only [h0, h210, h243, h244, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                  · linarith only [h238, h239, h244, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h238, h243, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h248 | h248
            · linarith only [h1, h2, h238, h248, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h250 | h250
              · linarith only [h1, h2, h250, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h252 | h252
                · rcases m.htr 1 2 3 (by decide) (by decide) with h253 | h253
                  · linarith only [h0, h238, h253, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h255 | h255
                    · linarith only [h0, h248, h252, h255, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h257 | h257
                      · linarith only [h1, h210, h253, h257, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h259 | h259
                        · linarith only [h1, h2, h238, h250, h255, h259, hc02, hc24, hlam, hphi]
                        · linarith only [h1, h2, h259, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h2, h252, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h263 | h263
      · rcases m.htr 0 1 5 (by decide) (by decide) with h264 | h264
        · rcases m.htr 0 2 3 (by decide) (by decide) with h265 | h265
          · linarith only [h0, h1, h265, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h267 | h267
            · rcases m.htr 0 3 4 (by decide) (by decide) with h268 | h268
              · rcases m.htr 0 4 5 (by decide) (by decide) with h269 | h269
                · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
                  · linarith only [h265, h267, h270, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h272 | h272
                    · linarith only [h0, h272, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                    · linarith only [h0, h1, h267, h270, h272, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
                  · linarith only [h0, h275, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
                    · linarith only [h0, h1, h275, h277, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1, h267, h275, h277, hc12, hc23, hlam, hphi]
              · linarith only [h1, h263, h268, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h281 | h281
              · rcases m.htr 0 4 5 (by decide) (by decide) with h282 | h282
                · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
                  · linarith only [h0, h283, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h285 | h285
                    · linarith only [h0, h1, h267, h283, h285, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                            · linarith only [h1, h263, h283, h290, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h1, h263, h282, h283, h290, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                          · linarith only [h1, h263, h282, h289, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h1, h263, h281, h282, h288, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h296 | h296
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h297 | h297
                            · linarith only [h263, h297, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h282, h297, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                          · linarith only [h1, h263, h282, h296, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h1, h263, h295, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
                  · linarith only [h0, h302, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                    · linarith only [h0, h267, h304, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h306 | h306
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h308 | h308
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                            · linarith only [h1, h263, h282, h302, h309, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · linarith only [h304, h306, h309, hlam]
                          · linarith only [h1, h263, h304, h308, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h263, h281, h307, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h314 | h314
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h315 | h315
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h316 | h316
                            · linarith only [h263, h282, h316, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h318 | h318
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h319 | h319
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h320 | h320
                                  · linarith only [h263, h282, h314, h320, hlam]
                                  · rcases h1bigk with h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h1, h302, hc12, hc23, hlam, hphi, p322_1]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h1, hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h1, h302, h314, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p322_1, u3ehi3]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h1, h302, h314, h316, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p322_1, u3ehi3]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h0, hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h302, hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h304, hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h306, hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h0, h302, hc12, hc23, hlam, hphi, p322_1]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      rcases p322_3 (m.d 0 1) (by simp) with h334 | h334
                                      · linarith only [h1, h334, hlam]
                                      · linarith only [h0, h334, hlam]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      rcases p322_3 (m.d 0 1) (by simp) with h338 | h338
                                      · linarith only [h1, h338, hlam]
                                      · linarith only [h263, h338, hlam]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      rcases p322_3 (m.d 0 1) (by simp) with h341 | h341
                                      · linarith only [h1, h341, hlam]
                                      · linarith only [h264, h341, hlam]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h263, hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h264, h316, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p322_1, u0elo0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h314, hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h316, hlam, p322_1]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h264, hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h1, h264, h302, hc12, hc23, hlam, hphi, p322_1]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h315, hlam, p322_0]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [h1, h264, h302, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p322_1, u4ehi1]
                                    · have p322_0 := h322c.1
                                      have p322_1 := h322c.2.1
                                      have p322_2 := h322c.2.2.1
                                      have p322_3 := h322c.2.2.2
                                      linarith only [hlam, p322_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h354 | h354
                                  · linarith only [h0, h267, h319, h354, hc12, hc34, hlam, hphi, ht23]
                                  · rcases h1bigk with h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h1, h302, hc12, hc23, hlam, hphi, p356_1]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h1, hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h1, h302, h314, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p356_1, u3ehi3]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h1, h302, h306, hc12, hc23, hlam, hphi, p356_1]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h0, hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h302, hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h304, hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h306, hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h0, h302, hc12, hc23, hlam, hphi, p356_1]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      rcases p356_3 (m.d 0 1) (by simp) with h368 | h368
                                      · linarith only [h1, h368, hlam]
                                      · linarith only [h0, h368, hlam]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      rcases p356_3 (m.d 0 1) (by simp) with h372 | h372
                                      · linarith only [h1, h372, hlam]
                                      · linarith only [h263, h372, hlam]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      rcases p356_3 (m.d 0 1) (by simp) with h375 | h375
                                      · linarith only [h1, h375, hlam]
                                      · linarith only [h264, h375, hlam]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h263, hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h263, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p356_1, u0elo0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h314, hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h316, hlam, p356_1]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h264, hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h1, h264, h302, hc12, hc23, hlam, hphi, p356_1]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h315, hlam, p356_0]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [h1, h264, h302, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p356_1, u4ehi1]
                                    · have p356_0 := h356c.1
                                      have p356_1 := h356c.2.1
                                      have p356_2 := h356c.2.2.1
                                      have p356_3 := h356c.2.2.2
                                      linarith only [hlam, p356_0]
                              · linarith only [h1, h263, h264, h302, h314, h318, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h1, h263, h314, h315, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h263, h304, h314, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h263, h281, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h392 | h392
          · linarith only [h0, h1, h392, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h394 | h394
            · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
              · rcases m.htr 0 4 5 (by decide) (by decide) with h396 | h396
                · linarith only [h0, h264, h394, h396, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                  · linarith only [h392, h394, h398, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h400 | h400
                    · linarith only [h0, h1, h398, h400, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1, h394, h398, h400, hc12, hc23, hlam, hphi]
              · linarith only [h1, h263, h395, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h404 | h404
              · rcases m.htr 0 4 5 (by decide) (by decide) with h405 | h405
                · linarith only [h263, h264, h405, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h407 | h407
                  · linarith only [h0, h407, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h409 | h409
                    · linarith only [h0, h1, h394, h407, h409, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h411 | h411
                      · linarith only [h0, h264, h411, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h413 | h413
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h414 | h414
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h415 | h415
                            · linarith only [h263, h394, h405, h415, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h263, h264, h413, h415, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h1, h263, h413, h414, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h263, h413, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h1, h263, h404, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h421 | h421
        · rcases m.htr 0 2 3 (by decide) (by decide) with h422 | h422
          · linarith only [h0, h1, h422, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h424 | h424
            · linarith only [h0, h263, h424, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h426 | h426
              · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
                · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                  · linarith only [h0, h422, h428, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
                    · linarith only [h0, h424, h427, h430, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h432 | h432
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h434 | h434
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h435 | h435
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h436 | h436
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h437 | h437
                                · linarith only [h0, h263, h428, h432, h433, h437, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                · linarith only [h0, h263, h430, h437, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h0, h263, h426, h428, h432, h433, h434, h436, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                            · linarith only [h0, h263, h432, h434, h435, hc45, hlam, hphi, ht34, u3ehi4]
                          · linarith only [h0, h263, h433, h434, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h426, h433, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h446 | h446
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h448 | h448
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h449 | h449
                                  · linarith only [h426, h449, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                  · linarith only [h427, h449, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                                · linarith only [h263, h421, h430, h446, h448, hlam]
                              · linarith only [h263, h421, h428, h444, h445, h447, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h263, h421, h445, h446, hc45, hlam, hphi, ht34, u3ehi4]
                          · linarith only [h263, h421, h432, h444, h445, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h426, h444, hlam]
                · linarith only [h263, h421, h427, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h458 | h458
                · rcases m.htr 1 2 3 (by decide) (by decide) with h459 | h459
                  · linarith only [h0, h1, h459, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h461 | h461
                    · linarith only [h0, h1, h426, h461, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h463 | h463
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h464 | h464
                        · linarith only [h0, h1, h426, h459, h464, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h463, h464, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h467 | h467
                        · linarith only [h1, h421, h426, h459, h463, h467, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h421, h463, h467, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h263, h421, h458, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h471 | h471
          · linarith only [h0, h1, h471, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h473 | h473
            · linarith only [h0, h263, h473, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h475 | h475
              · rcases m.htr 0 4 5 (by decide) (by decide) with h476 | h476
                · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
                  · linarith only [h0, h471, h477, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
                    · linarith only [h0, h421, h473, h476, h479, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h481 | h481
                      · linarith only [h0, h421, h481, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h483 | h483
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h484 | h484
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h485 | h485
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h486 | h486
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h488 | h488
                                  · linarith only [h475, h488, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                  · linarith only [h476, h488, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                                · linarith only [h263, h476, h479, h487, hlam]
                              · linarith only [h0, h421, h477, h483, h485, h486, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h263, h476, h485, hlam]
                          · linarith only [h1, h475, h484, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h475, h483, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h496 | h496
                  · linarith only [h0, h496, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h498 | h498
                    · linarith only [h0, h498, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
                      · linarith only [h0, h421, h500, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h502 | h502
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h503 | h503
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h504 | h504
                            · linarith only [h0, h263, h476, h496, h502, h504, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h263, h504, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h503, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h475, h502, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h509 | h509
                · rcases m.htr 1 2 3 (by decide) (by decide) with h510 | h510
                  · linarith only [h0, h510, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h512 | h512
                    · linarith only [h0, h1, h475, h512, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h514 | h514
                      · linarith only [h0, h421, h514, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
                        · linarith only [h0, h1, h475, h510, h516, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h516, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h519 | h519
                  · linarith only [h0, h519, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h521 | h521
                    · linarith only [h0, h1, h475, h509, h521, hc45, hlam, hphi, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h523 | h523
                      · linarith only [h0, h421, h523, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h525 | h525
                        · linarith only [h0, h1, h475, h519, h525, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h525, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h528 | h528
    · rcases m.htr 0 1 4 (by decide) (by decide) with h529 | h529
      · rcases m.htr 0 1 5 (by decide) (by decide) with h530 | h530
        · rcases m.htr 0 2 3 (by decide) (by decide) with h531 | h531
          · rcases m.htr 0 2 4 (by decide) (by decide) with h532 | h532
            · rcases m.htr 0 3 4 (by decide) (by decide) with h533 | h533
              · rcases m.htr 0 4 5 (by decide) (by decide) with h534 | h534
                · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h536 | h536
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h537 | h537
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h538 | h538
                        · linarith only [h528, h538, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h533, h538, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h529, h537, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h528, h533, h536, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h528, h533, h535, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h545 | h545
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h546 | h546
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h547 | h547
                        · linarith only [h528, h547, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h533, h547, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h528, h533, h546, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h528, h533, h545, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h528, h533, h544, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h553 | h553
                · rcases m.htr 1 2 3 (by decide) (by decide) with h554 | h554
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h555 | h555
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h556 | h556
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h557 | h557
                        · linarith only [h528, h533, h557, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h559 | h559
                          · linarith only [h0, h528, h559, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h561 | h561
                            · linarith only [h0, h529, h561, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h529, h553, h557, h561, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h529, h553, h556, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h528, h554, h555, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h528, h554, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h567 | h567
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h568 | h568
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h570 | h570
                        · linarith only [h528, h570, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h572 | h572
                          · linarith only [h0, h528, h572, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h574 | h574
                            · linarith only [h0, h529, h533, h553, h574, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h576 | h576
                              · linarith only [h528, h533, h567, h576, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h578 | h578
                                · linarith only [h529, h553, h568, h578, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h580 | h580
                                  · linarith only [h528, h533, h553, h567, h580, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h528, h533, h567, h580, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h528, h567, h569, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h528, h532, h567, h568, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                  · linarith only [h0, h528, h567, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h0, h529, h532, hlam]
          · linarith only [h0, h528, h531, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h588 | h588
          · rcases m.htr 0 2 4 (by decide) (by decide) with h589 | h589
            · rcases m.htr 0 3 4 (by decide) (by decide) with h590 | h590
              · rcases m.htr 0 4 5 (by decide) (by decide) with h591 | h591
                · linarith only [h528, h530, h590, h591, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h593 | h593
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h594 | h594
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h595 | h595
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h596 | h596
                        · linarith only [h528, h596, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h590, h596, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h528, h590, h595, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h528, h590, h594, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h528, h590, h593, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h602 | h602
                · linarith only [h529, h530, h602, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h605 | h605
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h606 | h606
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h607 | h607
                        · linarith only [h528, h590, h607, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h609 | h609
                          · linarith only [h528, h590, h609, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h528, h530, h609, hc35, hlam, hphi, u3ehi1]
                      · linarith only [h0, h528, h604, h606, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h528, h604, h605, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h528, h604, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h0, h529, h589, hlam]
          · linarith only [h0, h528, h588, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h617 | h617
        · rcases m.htr 0 2 3 (by decide) (by decide) with h618 | h618
          · rcases m.htr 0 2 4 (by decide) (by decide) with h619 | h619
            · rcases m.htr 0 3 4 (by decide) (by decide) with h620 | h620
              · linarith only [h528, h529, h620, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h622 | h622
                · rcases m.htr 1 2 3 (by decide) (by decide) with h623 | h623
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h624 | h624
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h626 | h626
                        · linarith only [h528, h620, h626, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · linarith only [h528, h529, h623, h626, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h528, h529, h623, h624, h625, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h528, h619, h623, h624, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                  · linarith only [h0, h528, h623, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h528, h529, h622, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h633 | h633
              · linarith only [h0, h528, h619, h633, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h635 | h635
                · rcases m.htr 1 2 3 (by decide) (by decide) with h636 | h636
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h637 | h637
                    · linarith only [h0, h528, h619, h636, h637, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h528, h636, h637, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h528, h636, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h528, h619, h635, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h528, h618, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h643 | h643
          · rcases m.htr 0 2 4 (by decide) (by decide) with h644 | h644
            · rcases m.htr 0 3 4 (by decide) (by decide) with h645 | h645
              · linarith only [h528, h529, h645, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h647 | h647
                · rcases m.htr 1 2 3 (by decide) (by decide) with h648 | h648
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h649 | h649
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h650 | h650
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h651 | h651
                        · linarith only [h528, h645, h651, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · linarith only [h528, h529, h648, h651, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h528, h529, h648, h649, h650, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h528, h644, h648, h649, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                  · linarith only [h0, h528, h648, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h528, h529, h647, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h658 | h658
              · linarith only [h0, h528, h644, h658, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h660 | h660
                · rcases m.htr 1 2 3 (by decide) (by decide) with h661 | h661
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h662 | h662
                    · linarith only [h0, h528, h644, h661, h662, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h528, h661, h662, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h528, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h528, h644, h660, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h528, h643, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h668 | h668
      · rcases m.htr 0 1 5 (by decide) (by decide) with h669 | h669
        · rcases m.htr 0 2 3 (by decide) (by decide) with h670 | h670
          · rcases m.htr 0 2 4 (by decide) (by decide) with h671 | h671
            · rcases m.htr 0 3 4 (by decide) (by decide) with h672 | h672
              · rcases m.htr 0 4 5 (by decide) (by decide) with h673 | h673
                · rcases m.htr 1 2 3 (by decide) (by decide) with h674 | h674
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h675 | h675
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h676 | h676
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h677 | h677
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h679 | h679
                            · linarith only [h668, h679, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h528, h668, h670, h673, h677, h679, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                          · linarith only [h528, h668, h673, h678, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h528, h668, h670, h672, h673, h677, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · linarith only [h528, h668, h673, h674, h676, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h528, h668, h673, h674, h675, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h668, h673, h674, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h687 | h687
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h688 | h688
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h689 | h689
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h690 | h690
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h691 | h691
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h692 | h692
                            · linarith only [h528, h668, h673, h687, h692, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h694 | h694
                              · linarith only [h670, h694, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                              · linarith only [h672, h694, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                          · linarith only [h528, h668, h690, h691, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h528, h668, h672, h688, h690, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                      · linarith only [h528, h668, h687, h688, h689, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h528, h668, h687, h688, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h668, h687, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h528, h668, h672, hlam]
            · linarith only [h0, h668, h671, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h704 | h704
            · rcases m.htr 0 3 4 (by decide) (by decide) with h705 | h705
              · rcases m.htr 0 4 5 (by decide) (by decide) with h706 | h706
                · rcases m.htr 1 2 3 (by decide) (by decide) with h707 | h707
                  · linarith only [h670, h704, h707, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h668, h706, h707, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h710 | h710
                  · linarith only [h0, h668, h670, h710, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h668, h710, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h528, h668, h705, hlam]
            · linarith only [h0, h668, h704, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h715 | h715
          · rcases m.htr 0 2 4 (by decide) (by decide) with h716 | h716
            · rcases m.htr 0 3 4 (by decide) (by decide) with h717 | h717
              · rcases m.htr 0 4 5 (by decide) (by decide) with h718 | h718
                · linarith only [h668, h669, h718, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h720 | h720
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h721 | h721
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h722 | h722
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h723 | h723
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h724 | h724
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h725 | h725
                            · linarith only [h668, h669, h718, h720, h724, h725, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · linarith only [h668, h669, h723, h725, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h528, h668, h723, h724, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h528, h668, h723, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                      · linarith only [h528, h668, h720, h721, h722, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h528, h668, h720, h721, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h668, h715, h720, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
              · linarith only [h528, h668, h717, hlam]
            · linarith only [h0, h668, h716, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h735 | h735
            · rcases m.htr 0 3 4 (by decide) (by decide) with h736 | h736
              · rcases m.htr 0 4 5 (by decide) (by decide) with h737 | h737
                · linarith only [h668, h669, h737, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h739 | h739
                  · linarith only [h715, h735, h739, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h668, h739, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h668, h715, h736, hlam]
            · linarith only [h0, h668, h735, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h744 | h744
        · rcases m.htr 0 2 3 (by decide) (by decide) with h745 | h745
          · rcases m.htr 0 2 4 (by decide) (by decide) with h746 | h746
            · rcases m.htr 0 3 4 (by decide) (by decide) with h747 | h747
              · rcases m.htr 0 4 5 (by decide) (by decide) with h748 | h748
                · rcases m.htr 1 2 3 (by decide) (by decide) with h749 | h749
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h750 | h750
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h751 | h751
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h752 | h752
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h753 | h753
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h754 | h754
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h755 | h755
                              · linarith only [h745, h755, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                              · linarith only [h747, h755, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · linarith only [h668, h744, h753, h754, hc45, hlam, hphi, ht34, u3ehi4]
                          · linarith only [h528, h747, h753, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h528, h747, h752, hlam]
                      · linarith only [h0, h744, h745, h747, h751, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h0, h746, h750, hlam]
                  · linarith only [h0, h745, h749, hlam]
                · linarith only [h668, h744, h748, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h765 | h765
                · rcases m.htr 1 2 3 (by decide) (by decide) with h766 | h766
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h767 | h767
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h768 | h768
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h769 | h769
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h770 | h770
                          · linarith only [h528, h744, h747, h766, h769, h770, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h528, h747, h769, h770, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h773 | h773
                          · linarith only [h769, h773, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h528, h744, h773, hlam]
                      · linarith only [h0, h744, h745, h768, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h528, h746, h766, h767, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h745, h766, hlam]
                · linarith only [h668, h744, h765, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h780 | h780
              · linarith only [h745, h746, h780, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h782 | h782
                · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
                    · linarith only [h745, h746, h784, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h786 | h786
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h787 | h787
                        · linarith only [h780, h783, h784, h787, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h789 | h789
                          · linarith only [h787, h789, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h528, h744, h789, hlam]
                      · linarith only [h0, h744, h786, hlam]
                  · linarith only [h0, h745, h783, hlam]
                · linarith only [h745, h746, h782, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h795 | h795
            · rcases m.htr 0 3 4 (by decide) (by decide) with h796 | h796
              · rcases m.htr 0 4 5 (by decide) (by decide) with h797 | h797
                · rcases m.htr 1 2 3 (by decide) (by decide) with h798 | h798
                  · linarith only [h745, h795, h797, h798, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h800 | h800
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h801 | h801
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h802 | h802
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h803 | h803
                          · linarith only [h668, h744, h798, h800, h803, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h528, h796, h803, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h528, h796, h802, hlam]
                      · linarith only [h668, h744, h800, h801, hlam]
                    · linarith only [h0, h744, h795, h800, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h668, h744, h797, hlam]
              · linarith only [h745, h795, h796, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h811 | h811
              · rcases m.htr 0 4 5 (by decide) (by decide) with h812 | h812
                · rcases m.htr 1 2 3 (by decide) (by decide) with h813 | h813
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h814 | h814
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h815 | h815
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h816 | h816
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h817 | h817
                          · linarith only [h0, h744, h745, h813, h817, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h528, h811, h817, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h745, h811, h813, h816, hlam]
                      · linarith only [h745, h811, h813, h815, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h745, h813, h814, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h823 | h823
                    · linarith only [h0, h744, h795, h812, h813, h823, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h825 | h825
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h826 | h826
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h827 | h827
                          · linarith only [h0, h744, h813, h827, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h528, h811, h827, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h528, h811, h826, hlam]
                      · linarith only [h0, h744, h825, hlam]
                · linarith only [h668, h744, h812, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h833 | h833
                · rcases m.htr 1 2 3 (by decide) (by decide) with h834 | h834
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h835 | h835
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h836 | h836
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h837 | h837
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h838 | h838
                          · linarith only [h528, h744, h811, h834, h837, h838, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h0, h745, h811, h837, h838, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                          · linarith only [h837, h841, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h0, h744, h745, h834, h841, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h745, h834, h836, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h744, h745, h833, h834, h835, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h846 | h846
                    · linarith only [h0, h744, h795, h833, h834, h846, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h848 | h848
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h849 | h849
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h850 | h850
                          · linarith only [h0, h744, h846, h850, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h0, h745, h811, h849, h850, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h853 | h853
                          · linarith only [h849, h853, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h0, h744, h834, h853, hlam]
                      · linarith only [h0, h744, h848, hlam]
                · linarith only [h668, h744, h833, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h858 | h858
          · rcases m.htr 0 2 4 (by decide) (by decide) with h859 | h859
            · rcases m.htr 0 3 4 (by decide) (by decide) with h860 | h860
              · rcases m.htr 0 4 5 (by decide) (by decide) with h861 | h861
                · rcases m.htr 1 2 3 (by decide) (by decide) with h862 | h862
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h863 | h863
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h864 | h864
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h865 | h865
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h866 | h866
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h867 | h867
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h868 | h868
                              · linarith only [h858, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                              · linarith only [h860, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · linarith only [h861, h867, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                          · linarith only [h528, h860, h866, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h528, h860, h865, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h874 | h874
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h875 | h875
                          · linarith only [h862, h864, h875, hlam]
                          · linarith only [h528, h860, h875, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h528, h860, h874, hlam]
                    · linarith only [h0, h859, h863, hlam]
                  · linarith only [h0, h858, h862, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h881 | h881
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h882 | h882
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h883 | h883
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h884 | h884
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h885 | h885
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h886 | h886
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h887 | h887
                              · linarith only [h858, h887, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                              · linarith only [h860, h887, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h890 | h890
                              · linarith only [h858, h890, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                              · linarith only [h668, h860, h886, h890, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h528, h860, h885, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h528, h860, h884, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h895 | h895
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h896 | h896
                          · linarith only [h881, h883, h896, hlam]
                          · linarith only [h528, h860, h896, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h528, h860, h895, hlam]
                    · linarith only [h0, h859, h882, hlam]
                  · linarith only [h0, h858, h881, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h902 | h902
                · rcases m.htr 1 2 3 (by decide) (by decide) with h903 | h903
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h904 | h904
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h905 | h905
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h906 | h906
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h907 | h907
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h908 | h908
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h909 | h909
                              · linarith only [h858, h860, h909, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h911 | h911
                                · linarith only [h859, h911, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                · linarith only [h902, h911, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                            · linarith only [h860, h902, h903, h906, h908, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                          · linarith only [h906, h907, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h916 | h916
                          · linarith only [h906, h916, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h918 | h918
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h919 | h919
                              · linarith only [h858, h906, h919, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h921 | h921
                                · linarith only [h859, h921, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                · linarith only [h902, h921, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                            · linarith only [h668, h902, h918, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h925 | h925
                        · linarith only [h858, h860, h903, h905, h925, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h927 | h927
                          · linarith only [h925, h927, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h929 | h929
                            · linarith only [h904, h905, h929, hlam]
                            · linarith only [h902, h929, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · linarith only [h0, h859, h904, hlam]
                  · linarith only [h0, h858, h859, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h934 | h934
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h935 | h935
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h936 | h936
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h937 | h937
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h938 | h938
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h939 | h939
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h940 | h940
                              · linarith only [h858, h860, h940, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h942 | h942
                                · linarith only [h859, h902, h942, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h944 | h944
                                  · linarith only [h858, h860, h902, h944, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h858, h860, h934, h937, h939, h944, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h858, h860, h937, h939, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h858, h860, h937, h938, hc35, hlam, hphi, u3ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h949 | h949
                          · linarith only [h937, h949, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h951 | h951
                            · linarith only [h858, h860, h902, h937, h951, hc34, hlam, hphi, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h953 | h953
                              · linarith only [h528, h858, h937, h951, h953, hc45, hlam, hphi, ht34, u3ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h955 | h955
                                · linarith only [h528, h937, h951, h955, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h957 | h957
                                  · linarith only [h528, h937, h951, h957, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h860, h957, hc45, hlam, hphi, ht34, u3ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h960 | h960
                        · linarith only [h858, h860, h934, h936, h960, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h962 | h962
                          · linarith only [h960, h962, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h964 | h964
                            · linarith only [h858, h860, h902, h935, h936, h964, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h966 | h966
                              · linarith only [h528, h858, h960, h964, h966, hc45, hlam, hphi, ht34, u3ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h968 | h968
                                · linarith only [h0, h528, h859, h936, h960, h964, h968, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                                · linarith only [h0, h859, h936, h966, h968, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h0, h859, h935, hlam]
                  · linarith only [h0, h858, h934, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h973 | h973
              · linarith only [h858, h859, h973, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h975 | h975
                · rcases m.htr 1 2 3 (by decide) (by decide) with h976 | h976
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h977 | h977
                    · linarith only [h858, h859, h977, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h979 | h979
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h980 | h980
                        · linarith only [h973, h976, h977, h980, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h982 | h982
                          · linarith only [h980, h982, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h985 | h985
                              · linarith only [h858, h980, h985, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                              · linarith only [h0, h858, h977, h985, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h668, h858, h859, h984, hc45, hlam, hphi, ht34, u3ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h989 | h989
                        · linarith only [h858, h859, h973, h976, h977, h989, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h991 | h991
                          · linarith only [h989, h991, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h993 | h993
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h994 | h994
                              · linarith only [h858, h989, h994, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                              · linarith only [h0, h858, h977, h994, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h668, h975, h993, hlam]
                  · linarith only [h0, h858, h976, hlam]
                · linarith only [h858, h859, h975, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1000 | h1000
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1001 | h1001
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1002 | h1002
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1003 | h1003
                  · linarith only [h1000, h1003, h858, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1005 | h1005
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1006 | h1006
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1007 | h1007
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1008 | h1008
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1009 | h1009
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1010 | h1010
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1011 | h1011
                                · linarith only [h1000, h1011, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                · linarith only [h1002, h1011, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                              · linarith only [h1002, h1003, h1005, h1010, h668, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h1002, h1009, h668, hlam]
                          · linarith only [h1001, h1008, h528, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1001, h1007, h528, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1018 | h1018
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1019 | h1019
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1020 | h1020
                            · linarith only [h1005, h1006, h1020, hlam]
                            · linarith only [h1002, h1020, h668, hlam]
                          · linarith only [h1001, h1019, h528, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1001, h1018, h528, hlam]
                    · linarith only [h0, h1000, h1005, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1026 | h1026
                  · linarith only [h1000, h1026, h858, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1028 | h1028
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1029 | h1029
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1030 | h1030
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1031 | h1031
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1032 | h1032
                            · linarith only [h1002, h1026, h1028, h1032, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1034 | h1034
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1035 | h1035
                                · linarith only [h0, h1000, h1026, h1032, h1035, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1037 | h1037
                                  · linarith only [h0, h1000, h1026, h1032, h1034, h1037, h668, hc01, hc23, hlam, hphi, ht12]
                                  · rcases h1bigk with h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h0, hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h528, hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h668, hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h744, hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1026, hc01, hc23, hlam, hphi, ht12, p1039_1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1026, hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1026, h668, hc01, hc23, hlam, hphi, ht12, p1039_1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1026, h744, hc01, hc23, hlam, hphi, ht12, p1039_1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      rcases p1039_3 (m.d 0 1) (by simp) with h1050 | h1050
                                      · linarith only [h1050, hlam, p1039_0]
                                      · rcases p1039_3 (m.d 1 2) (by simp) with h1052 | h1052
                                        · linarith only [h1026, h1052, hlam]
                                        · linarith only [h0, h1052, hlam]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h0, h1000, h1034, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1039_1, u3ehi3]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1026, h668, hc01, hc23, hlam, hphi, ht12, p1039_1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1026, h1032, h668, hc01, hc23, hlam, hphi, ht12, p1039_1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1032, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1039_1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1028, hlam, p1039_1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1030, hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1032, hlam, p1039_1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1026, h1029, hc01, hc23, hlam, hphi, ht12, p1039_1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1029, hlam, p1039_1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1031, hlam, p1039_0]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [h1026, h1029, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1039_1, u4ehi1]
                                    · have p1039_0 := h1039c.1
                                      have p1039_1 := h1039c.2.1
                                      have p1039_2 := h1039c.2.2.1
                                      have p1039_3 := h1039c.2.2.2
                                      linarith only [hlam, p1039_0]
                              · linarith only [h0, h1000, h1001, h1002, h1026, h1034, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi2]
                          · linarith only [h1001, h1031, h528, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1001, h1030, h528, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1072 | h1072
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1073 | h1073
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1074 | h1074
                            · linarith only [h1002, h1026, h1028, h1074, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1076 | h1076
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1077 | h1077
                                · linarith only [h1000, h1074, h1077, h668, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                · linarith only [h0, h1000, h1029, h1076, h1077, hc45, hlam, hphi, ht34, u3ehi3]
                              · linarith only [h0, h1000, h1026, h1076, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                          · linarith only [h1001, h1073, h528, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1001, h1072, h528, hlam]
                    · linarith only [h0, h1000, h1028, hlam]
              · linarith only [h1000, h1001, h858, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1085 | h1085
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1086 | h1086
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1087 | h1087
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1088 | h1088
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1089 | h1089
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1090 | h1090
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1091 | h1091
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1092 | h1092
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1093 | h1093
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1094 | h1094
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1095 | h1095
                                  · linarith only [h1085, h1095, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                  · linarith only [h1086, h1095, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                                · linarith only [h1000, h1086, h1094, hlam]
                              · linarith only [h1085, h1093, h858, hlam]
                            · linarith only [h1000, h1086, h1088, h1092, hlam]
                          · linarith only [h1085, h1087, h1091, h858, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1085, h1087, h1090, h858, hlam]
                      · linarith only [h1085, h1087, h1089, h858, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1085, h1087, h1088, h858, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1105 | h1105
                    · linarith only [h1000, h1087, h1105, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1107 | h1107
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1108 | h1108
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1109 | h1109
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1110 | h1110
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1111 | h1111
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1112 | h1112
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1113 | h1113
                                  · linarith only [h1085, h1113, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                  · linarith only [h1105, h1107, h1111, h1112, h1113, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                · linarith only [h1085, h1086, h1105, h1107, h1112, h744, hc05, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h1085, h1111, h858, hlam]
                            · linarith only [h1086, h1087, h1107, h1110, h668, h744, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h1085, h1109, h528, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1085, h1108, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1121 | h1121
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1122 | h1122
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1123 | h1123
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1124 | h1124
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1125 | h1125
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1126 | h1126
                                  · linarith only [h1085, h1126, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                  · linarith only [h1086, h1126, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                                · linarith only [h1086, h1105, h1125, h668, hlam]
                              · linarith only [h1087, h1122, h1124, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h1086, h1123, h668, hlam]
                          · linarith only [h1085, h1122, h528, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1085, h1121, h528, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1134 | h1134
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1135 | h1135
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1136 | h1136
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1137 | h1137
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1138 | h1138
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1139 | h1139
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1140 | h1140
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1141 | h1141
                                · linarith only [h1085, h1086, h1134, h1140, h1141, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h1000, h1137, h1139, h1141, hc01, hc13, hlam, hphi]
                              · linarith only [h1085, h1086, h1134, h1137, h1139, h1140, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1145 | h1145
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1146 | h1146
                                · linarith only [h1139, h1146, h668, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1148 | h1148
                                  · linarith only [h0, h1000, h1085, h1134, h1135, h1139, h1148, h858, hc01, hc12, hlam, hphi]
                                  · rcases h1bigk with h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h0, hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h528, hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h668, hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h744, hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      rcases p1150_3 (m.d 0 1) (by simp) with h1156 | h1156
                                      · linarith only [h1156, hlam, p1150_0]
                                      · rcases p1150_3 (m.d 1 2) (by simp) with h1158 | h1158
                                        · rcases p1150_3 (m.d 1 3) (by simp) with h1159 | h1159
                                          · linarith only [h1134, h1159, hlam]
                                          · linarith only [h1159, h528, hlam]
                                        · linarith only [h1158, hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h528, hc01, hc12, hlam, hphi, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h0, h1000, h1135, hc01, hc12, hlam, hphi, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h744, hc01, hc12, hlam, hphi, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      rcases p1150_3 (m.d 0 1) (by simp) with h1167 | h1167
                                      · linarith only [h1167, hlam, p1150_0]
                                      · rcases p1150_3 (m.d 1 2) (by simp) with h1169 | h1169
                                        · rcases p1150_3 (m.d 1 3) (by simp) with h1170 | h1170
                                          · rcases p1150_3 (m.d 1 4) (by simp) with h1171 | h1171
                                            · linarith only [h1137, h1171, hlam]
                                            · linarith only [h1171, h668, hlam]
                                          · linarith only [h1170, hlam, p1150_0]
                                        · linarith only [h0, h1169, hlam]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h1134, hlam, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h0, h1000, h1135, hc01, hc13, hlam, hphi, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h0, h1000, h1134, h1135, h1139, hc01, hc12, hlam, hphi, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h1139, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h1135, hlam, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h1137, hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h1139, hlam, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      rcases p1150_3 (m.d 0 1) (by simp) with h1185 | h1185
                                      · linarith only [h1185, hlam, p1150_0]
                                      · rcases p1150_3 (m.d 1 2) (by simp) with h1187 | h1187
                                        · rcases p1150_3 (m.d 1 3) (by simp) with h1188 | h1188
                                          · rcases p1150_3 (m.d 1 4) (by simp) with h1189 | h1189
                                            · linarith only [h1139, h1189, hlam]
                                            · linarith only [h1189, h668, hlam]
                                          · linarith only [h1188, h528, hlam]
                                        · linarith only [h0, h1187, hlam]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h1136, hlam, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h1138, hlam, p1150_0]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [h668, hc01, hc15, hlam, hphi, p1150_1]
                                    · have p1150_0 := h1150c.1
                                      have p1150_1 := h1150c.2.1
                                      have p1150_2 := h1150c.2.2.1
                                      have p1150_3 := h1150c.2.2.2
                                      linarith only [hlam, p1150_0]
                              · linarith only [h1085, h1145, h858, hlam]
                          · linarith only [h1085, h1138, h528, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1085, h1134, h1137, h858, hlam]
                      · linarith only [h1085, h1134, h1136, h858, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1085, h1134, h1135, h858, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1203 | h1203
                    · linarith only [h0, h1000, h1134, h1203, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1205 | h1205
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1206 | h1206
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1207 | h1207
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1208 | h1208
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1209 | h1209
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1210 | h1210
                                · linarith only [h1085, h1086, h1203, h1205, h1209, h1210, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1203, h1205, h1206, h1208, h1210, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h1085, h1086, h1134, h1206, h1208, h1209, hlam]
                            · linarith only [h1203, h1205, h1208, hlam]
                          · linarith only [h1085, h1207, h528, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1085, h1206, h528, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1217 | h1217
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1218 | h1218
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1219 | h1219
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1220 | h1220
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1221 | h1221
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1222 | h1222
                                  · linarith only [h1085, h1086, h1222, hlam]
                                  · rcases h1bigk with h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h0, hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h528, hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h668, hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h744, hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h1205, hc01, hc25, hlam, hphi, ht12, p1224_1]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h1134, hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h1203, hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h1205, hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      rcases p1224_3 (m.d 0 1) (by simp) with h1235 | h1235
                                      · linarith only [h1235, hlam, p1224_0]
                                      · rcases p1224_3 (m.d 1 2) (by simp) with h1237 | h1237
                                        · linarith only [h1134, h1237, hlam]
                                        · linarith only [h0, h1237, hlam]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h0, h1134, hc01, hc23, hlam, hphi, ht12, p1224_1]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h1085, h1086, h1134, h1219, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1224_1, u3ehi3]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h0, h1134, h1205, hc01, hc23, hlam, hphi, ht12, p1224_1]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      rcases p1224_3 (m.d 0 1) (by simp) with h1244 | h1244
                                      · linarith only [h1244, hlam, p1224_0]
                                      · rcases p1224_3 (m.d 1 2) (by simp) with h1246 | h1246
                                        · linarith only [h1203, h1246, hlam]
                                        · linarith only [h0, h1246, hlam]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h0, hc01, hc14, hlam, hphi, p1224_1]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h1217, hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h1085, h1086, h1203, h1219, h1220, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1224_1, u3ehi3]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      rcases p1224_3 (m.d 0 1) (by simp) with h1253 | h1253
                                      · linarith only [h1253, hlam, p1224_0]
                                      · rcases p1224_3 (m.d 1 2) (by simp) with h1255 | h1255
                                        · linarith only [h1205, h1255, hlam]
                                        · linarith only [h0, h1255, hlam]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h0, hc01, hc15, hlam, hphi, p1224_1]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h1218, hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [h1219, hlam, p1224_0]
                                    · have p1224_0 := h1224c.1
                                      have p1224_1 := h1224c.2.1
                                      have p1224_2 := h1224c.2.2.1
                                      have p1224_3 := h1224c.2.2.2
                                      linarith only [hlam, p1224_0]
                                · linarith only [h0, h1203, h1221, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h1085, h1086, h1134, h1217, h1219, h1220, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1264 | h1264
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1265 | h1265
                                · linarith only [h1219, h1265, h668, hc01, hc24, hlam, hphi, ht12]
                                · linarith only [h0, h1203, h1265, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h1085, h1134, h1264, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h1085, h1218, h528, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1085, h1217, h528, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1271 | h1271
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1272 | h1272
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1273 | h1273
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1274 | h1274
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1275 | h1275
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1276 | h1276
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1277 | h1277
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1278 | h1278
                              · linarith only [h1085, h1272, h1278, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · linarith only [h0, h1272, h1275, h1278, h858, hc01, hc12, hlam, hphi]
                            · linarith only [h1271, h1277, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                          · linarith only [h1275, h1276, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1283 | h1283
                          · linarith only [h1275, h1283, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1285 | h1285
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1286 | h1286
                              · linarith only [h1275, h1286, h528, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1288 | h1288
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1289 | h1289
                                  · rcases h1bigk with h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [hlam, p1290_0]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h0, hlam, p1290_0]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h528, hlam, p1290_0]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h668, hlam, p1290_0]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h744, hlam, p1290_0]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      rcases p1290_3 (m.d 0 1) (by simp) with h1296 | h1296
                                      · linarith only [h1296, hlam, p1290_0]
                                      · rcases p1290_3 (m.d 1 2) (by simp) with h1298 | h1298
                                        · rcases p1290_3 (m.d 1 3) (by simp) with h1299 | h1299
                                          · linarith only [h1272, h1299, hlam]
                                          · linarith only [h1299, h528, hlam]
                                        · linarith only [h1298, hlam, p1290_0]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [hlam, p1290_0]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h0, h1272, h858, hc01, hc12, hlam, hphi, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h668, hc01, hc12, hlam, hphi, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h744, hc01, hc12, hlam, hphi, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h1283, h1289, hc01, hc34, hlam, hphi, ht12, ht23, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h1272, hlam, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [hlam, p1290_0]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h1275, hlam, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h1283, hlam, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      rcases p1290_3 (m.d 0 1) (by simp) with h1312 | h1312
                                      · linarith only [h1312, hlam, p1290_0]
                                      · rcases p1290_3 (m.d 1 2) (by simp) with h1314 | h1314
                                        · rcases p1290_3 (m.d 1 3) (by simp) with h1315 | h1315
                                          · linarith only [h1275, h1315, hlam]
                                          · linarith only [h1315, h528, hlam]
                                        · linarith only [h0, h1314, hlam]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h1273, hlam, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h0, h1272, h858, hc01, hc14, hlam, hphi, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [hlam, p1290_0]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h0, h1272, h1275, h1283, h858, hc01, hc34, hlam, hphi, ht12, ht23, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      rcases p1290_3 (m.d 0 1) (by simp) with h1323 | h1323
                                      · linarith only [h1323, hlam, p1290_0]
                                      · rcases p1290_3 (m.d 1 2) (by simp) with h1325 | h1325
                                        · rcases p1290_3 (m.d 1 3) (by simp) with h1326 | h1326
                                          · linarith only [h1283, h1326, hlam]
                                          · linarith only [h1326, h528, hlam]
                                        · linarith only [h0, h1325, hlam]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h1274, hlam, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h0, h1272, h858, hc01, hc15, hlam, hphi, p1290_1]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [h1285, hlam, p1290_0]
                                    · have p1290_0 := h1290c.1
                                      have p1290_1 := h1290c.2.1
                                      have p1290_2 := h1290c.2.2.1
                                      have p1290_3 := h1290c.2.2.2
                                      linarith only [hlam, p1290_0]
                                  · linarith only [h1271, h1275, h1289, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                                · linarith only [h1000, h1271, h1288, hlam]
                            · linarith only [h1000, h1271, h1273, h1285, hlam]
                      · linarith only [h1000, h1271, h1273, h1274, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h1272, h1273, h858, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1339 | h1339
                    · linarith only [h0, h1000, h1272, h1339, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1341 | h1341
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1342 | h1342
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1343 | h1343
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1344 | h1344
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1345 | h1345
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1346 | h1346
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1347 | h1347
                                  · rcases h1bigk with h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h0, hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h528, hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h668, hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h744, hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1339, h1345, hc01, hc23, hlam, hphi, ht12, p1348_1]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1272, hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1339, hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1339, h1343, h1345, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1348_1, u3ehi4]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      rcases p1348_3 (m.d 0 1) (by simp) with h1359 | h1359
                                      · linarith only [h1359, hlam, p1348_0]
                                      · rcases p1348_3 (m.d 1 2) (by simp) with h1361 | h1361
                                        · linarith only [h1272, h1361, hlam]
                                        · linarith only [h0, h1361, hlam]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h0, h1272, hc01, hc23, hlam, hphi, ht12, p1348_1]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1271, h1272, h668, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1348_1, u4ehi4]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1272, h744, hc01, hc23, hlam, hphi, ht12, p1348_1]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      rcases p1348_3 (m.d 0 1) (by simp) with h1368 | h1368
                                      · linarith only [h1368, hlam, p1348_0]
                                      · rcases p1348_3 (m.d 1 2) (by simp) with h1370 | h1370
                                        · linarith only [h1339, h1370, hlam]
                                        · linarith only [h0, h1370, hlam]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1341, h1346, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1348_1, u4ehi4]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1342, hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1339, h1345, h744, hc01, hc23, hlam, hphi, ht12, p1348_1]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1272, h1341, hc01, hc23, hlam, hphi, ht12, p1348_1]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1341, hlam, p1348_1]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1343, hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [h1344, hlam, p1348_0]
                                    · have p1348_0 := h1348c.1
                                      have p1348_1 := h1348c.2.1
                                      have p1348_2 := h1348c.2.2.1
                                      have p1348_3 := h1348c.2.2.2
                                      linarith only [hlam, p1348_0]
                                  · linarith only [h1085, h1271, h1347, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi0]
                                · linarith only [h1085, h1271, h1272, h1339, h1341, h1342, h1346, h744, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h1272, h1342, h1345, hlam]
                            · linarith only [h1085, h1271, h1272, h1342, h1344, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                          · linarith only [h1342, h1343, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1387 | h1387
                          · linarith only [h1342, h1387, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h1272, h1341, h1387, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1390 | h1390
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1391 | h1391
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1392 | h1392
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1393 | h1393
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1394 | h1394
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1395 | h1395
                                  · rcases h1bigk with h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h0, hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h528, hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h668, hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h744, hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h1341, h1394, hc01, hc24, hlam, hphi, ht12, p1396_1]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h1272, hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h1339, hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h1341, hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      rcases p1396_3 (m.d 0 1) (by simp) with h1407 | h1407
                                      · linarith only [h1407, hlam, p1396_0]
                                      · rcases p1396_3 (m.d 1 2) (by simp) with h1409 | h1409
                                        · linarith only [h1272, h1409, hlam]
                                        · linarith only [h0, h1409, hlam]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h0, hc01, hc13, hlam, hphi, p1396_1]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h1271, h1272, h668, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1396_1, u4ehi4]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h0, h1272, h1341, hc01, hc23, hlam, hphi, ht12, p1396_1]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      rcases p1396_3 (m.d 0 1) (by simp) with h1416 | h1416
                                      · linarith only [h1416, hlam, p1396_0]
                                      · rcases p1396_3 (m.d 1 2) (by simp) with h1418 | h1418
                                        · linarith only [h1339, h1418, hlam]
                                        · linarith only [h0, h1418, hlam]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h0, hc01, hc14, hlam, hphi, p1396_1]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h1390, hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h0, h1339, h1341, h1393, hc01, hc23, hlam, hphi, ht12, p1396_1]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      rcases p1396_3 (m.d 0 1) (by simp) with h1425 | h1425
                                      · linarith only [h1425, hlam, p1396_0]
                                      · rcases p1396_3 (m.d 1 2) (by simp) with h1427 | h1427
                                        · linarith only [h1341, h1427, hlam]
                                        · linarith only [h0, h1427, hlam]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h0, hc01, hc15, hlam, hphi, p1396_1]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h1391, hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [h1392, hlam, p1396_0]
                                    · have p1396_0 := h1396c.1
                                      have p1396_1 := h1396c.2.1
                                      have p1396_2 := h1396c.2.2.1
                                      have p1396_3 := h1396c.2.2.2
                                      linarith only [hlam, p1396_0]
                                  · linarith only [h1085, h1271, h1395, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi0]
                                · linarith only [h1085, h1271, h1272, h1339, h1390, h1394, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                              · linarith only [h1272, h1390, h1393, hlam]
                            · linarith only [h1085, h1271, h1272, h1390, h1392, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                          · linarith only [h1390, h1391, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1439 | h1439
                          · linarith only [h1390, h1439, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1441 | h1441
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1442 | h1442
                              · linarith only [h1390, h1442, h528, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1272, h1442, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1271, h1441, h668, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1446 | h1446
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1447 | h1447
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1448 | h1448
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1449 | h1449
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1450 | h1450
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1451 | h1451
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1452 | h1452
                              · linarith only [h1085, h1446, h1452, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · linarith only [h0, h1446, h1449, h1452, h858, hc01, hc12, hlam, hphi]
                            · linarith only [h1085, h1449, h1451, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1085, h1449, h1450, hc35, hlam, hphi, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1457 | h1457
                          · linarith only [h1449, h1457, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1459 | h1459
                            · linarith only [h1085, h1271, h1449, h1459, hc34, hlam, hphi, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1461 | h1461
                              · linarith only [h1446, h1449, h1459, h1461, hc45, hlam, hphi, u4ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1463 | h1463
                                · linarith only [h1447, h1459, h1463, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1465 | h1465
                                  · linarith only [h0, h1446, h1449, h1459, h1465, h858, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h1085, h1465, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h0, h1446, h1448, h858, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1446, h1447, h858, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1470 | h1470
                    · linarith only [h1000, h1446, h1470, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1472 | h1472
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1473 | h1473
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1474 | h1474
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1475 | h1475
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1476 | h1476
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1477 | h1477
                                · linarith only [h1085, h1271, h1446, h1472, h1477, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                                · linarith only [h0, h1470, h1475, h1477, hc01, hc15, hlam, hphi]
                              · linarith only [h1446, h1473, h1476, hlam]
                            · linarith only [h1085, h1473, h1475, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1085, h1473, h1474, hc35, hlam, hphi, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1483 | h1483
                          · linarith only [h1473, h1483, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h1446, h1472, h1483, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1486 | h1486
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1487 | h1487
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1488 | h1488
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1489 | h1489
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1490 | h1490
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1491 | h1491
                                  · linarith only [h1085, h1271, h1446, h1486, h1491, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                                  · linarith only [h1085, h1488, h1491, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · linarith only [h1470, h1488, h1490, hlam]
                              · linarith only [h0, h1446, h1489, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1085, h1486, h1488, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1085, h1486, h1487, hc35, hlam, hphi, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1498 | h1498
                          · linarith only [h1486, h1498, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1500 | h1500
                            · linarith only [h1085, h1271, h1486, h1500, hc34, hlam, hphi, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1502 | h1502
                              · linarith only [h1486, h1502, h528, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1446, h1502, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
