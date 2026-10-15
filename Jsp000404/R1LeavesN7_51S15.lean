import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5286000 in
set_option maxHeartbeats 5286000 in
theorem r1l7_20_12_14_M_LI_L_I_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                            · linarith only [h0, h10, h14, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                              · linarith only [h0, h14, h16, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                                · linarith only [h0, h11, h18, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h18, h9, hc24, hlam, hphi, u4elo0]
                          · linarith only [h13, h9, hc14, hlam, hphi, u4elo0]
                        · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h10, h11, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h10, h24, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                        · linarith only [h0, h10, h26, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                                  · linarith only [h0, h29, h32, h4, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h28, h32, hc34, hlam, hphi, u4elo1]
                                · linarith only [h24, h28, h31, hlam]
                              · linarith only [h0, h24, h28, h29, h30, h4, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h10, h29, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h28, h9, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                          · linarith only [h42, h9, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                            · linarith only [h0, h39, h44, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h44, h7, h9, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h0, h39, h41, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h39, h40, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                      · linarith only [h0, h39, h4, h49, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h49, h5, h9, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
                  · linarith only [h52, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                          · linarith only [h52, h57, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                            · linarith only [h0, h54, h59, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h52, h59, h7, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h0, h54, h56, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h54, h55, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                      · linarith only [h0, h4, h54, h64, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h5, h52, h64, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h67 | h67
                · rcases m.htr 0 4 5 (by decide) (by decide) with h68 | h68
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                            · linarith only [h0, h69, h7, h73, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                              · linarith only [h0, h70, h73, h75, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h67, h7, h75, hc23, hc34, hlam, hphi]
                          · linarith only [h68, h72, hc14, hlam, hphi, u4elo0]
                        · linarith only [h6, h67, h7, h71, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h69, h70, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h4, h69, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h67, h68, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h83 | h83
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                            · linarith only [h0, h84, h88, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                              · linarith only [h1, h67, h84, h90, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                                · linarith only [h0, h85, h92, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h2, h87, h92, hc24, hlam, hphi, u4elo0]
                          · linarith only [h7, h83, h87, hc14, hlam, hphi, u4elo3]
                        · linarith only [h0, h6, h84, h86, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h84, h85, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h4, h7, h84, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                          · linarith only [h102, h7, h83, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                            · linarith only [h1, h104, h7, h83, h99, hc34, hlam, hphi, u4elo4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                              · linarith only [h1, h106, h67, h99, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h108 | h108
                                · linarith only [h100, h108, h2, h83, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h110 | h110
                                  · linarith only [h110, h7, h83, hc03, hlam, hphi, ht34, u4elo3]
                                  · linarith only [h1, h110, h7, h99, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h0, h101, h6, h99, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h100, h99, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h4, h7, h99, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h116 | h116
              · rcases m.htr 0 3 5 (by decide) (by decide) with h117 | h117
                · linarith only [h117, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h119 | h119
                  · linarith only [h119, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                        · linarith only [h0, h123, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h125 | h125
                          · linarith only [h119, h125, h2, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                            · linarith only [h0, h121, h127, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h116, h117, h127, hc23, hc35, hlam, hphi]
                      · linarith only [h121, h122, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h119, h121, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h132 | h132
                · linarith only [h132, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                  · linarith only [h134, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h137 | h137
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                        · linarith only [h0, h138, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                          · linarith only [h134, h140, h2, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h142 | h142
                            · linarith only [h0, h136, h142, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h144 | h144
                              · linarith only [h0, h132, h137, h142, h144, h6, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h146 | h146
                                · linarith only [h0, h134, h137, h146, h6, hlam]
                                · linarith only [h0, h137, h142, h146, h6, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h136, h137, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h136, h4, h6, hc12, hc25, hlam, hphi]
          · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h152 | h152
          · rcases m.htr 0 2 5 (by decide) (by decide) with h153 | h153
            · rcases m.htr 0 3 4 (by decide) (by decide) with h154 | h154
              · rcases m.htr 0 3 5 (by decide) (by decide) with h155 | h155
                · rcases m.htr 0 4 5 (by decide) (by decide) with h156 | h156
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h157 | h157
                    · linarith only [h0, h152, h157, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h160 | h160
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h163 | h163
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                                · linarith only [h0, h159, h164, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h161, h162, h164, h2, hc34, hlam, hphi, u4elo0]
                              · linarith only [h155, h163, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1, h157, h159, h162, h4, hc24, hlam, hphi, u4elo3]
                          · linarith only [h156, h161, hc14, hlam, hphi, u4elo0]
                        · linarith only [h153, h160, h4, hc12, hc23, hlam, hphi]
                      · linarith only [h152, h159, h4, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h172 | h172
                    · linarith only [h0, h172, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
                          · linarith only [h156, h176, h2, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                                · linarith only [h156, h174, h180, h2, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h182 | h182
                                  · linarith only [h156, h174, h178, h182, h2, hlam]
                                  · rcases h0bigk with h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h0, h175, h180, hc24, hlam, hphi, ht0b, ht45, ht5b, p184_1, u0elo0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h1, h172, h175, h178, h180, hc34, hlam, hphi, ht0b, ht45, ht5b, p184_1, u0elo0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      rcases p184_3 (m.d 0 1) (by simp) with h188 | h188
                                      · rcases p184_3 (m.d 0 2) (by simp) with h189 | h189
                                        · linarith only [h0, h189, hlam]
                                        · linarith only [h152, h189, hlam]
                                      · linarith only [h188, h2, hlam]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      rcases p184_3 (m.d 0 1) (by simp) with h193 | h193
                                      · rcases p184_3 (m.d 0 2) (by simp) with h194 | h194
                                        · linarith only [h0, h194, hlam]
                                        · linarith only [h153, h194, hlam]
                                      · linarith only [h193, h3, hlam]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h0, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h4, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      rcases p184_3 (m.d 0 1) (by simp) with h201 | h201
                                      · rcases p184_3 (m.d 0 2) (by simp) with h202 | h202
                                        · rcases p184_3 (m.d 0 3) (by simp) with h203 | h203
                                          · rcases p184_3 (m.d 0 4) (by simp) with h204 | h204
                                            · linarith only [h152, h204, hlam]
                                            · rcases p184_3 (m.d 0 5) (by simp) with h206 | h206
                                              · linarith only [h153, h206, hlam]
                                              · linarith only [h156, h206, hlam]
                                          · linarith only [h154, h203, hlam]
                                        · linarith only [h152, h202, hlam]
                                      · linarith only [h2, h201, hlam]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      rcases p184_3 (m.d 0 1) (by simp) with h212 | h212
                                      · rcases p184_3 (m.d 0 2) (by simp) with h213 | h213
                                        · rcases p184_3 (m.d 0 3) (by simp) with h214 | h214
                                          · rcases p184_3 (m.d 0 4) (by simp) with h215 | h215
                                            · linarith only [h152, h215, hlam]
                                            · rcases p184_3 (m.d 0 5) (by simp) with h217 | h217
                                              · linarith only [h153, h217, hlam]
                                              · rcases h2bigk with h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h175, h178, h180, hc34, hlam, hphi, ht0b, ht45, ht5b, p219_1, u0elo1]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h4, hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  rcases p219_3 (m.d 0 2) (by simp) with h223 | h223
                                                  · rcases p219_3 (m.d 1 2) (by simp) with h224 | h224
                                                    · linarith only [h0, h224, hlam]
                                                    · linarith only [h174, h224, hlam]
                                                  · linarith only [h223, hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  rcases p219_3 (m.d 0 2) (by simp) with h228 | h228
                                                  · rcases p219_3 (m.d 1 2) (by simp) with h229 | h229
                                                    · linarith only [h0, h229, hlam]
                                                    · linarith only [h175, h229, hlam]
                                                  · linarith only [h228, hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h0, hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h172, hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h0, h178, hc34, hlam, hphi, ht0b, ht45, ht5b, p219_1, u0elo0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h1, h172, h178, h180, hc34, hlam, hphi, ht0b, ht45, ht5b, p219_1, u0elo0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h156, h174, h178, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p184_1, p219_1]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  rcases p219_3 (m.d 0 2) (by simp) with h239 | h239
                                                  · linarith only [h239, h4, hlam]
                                                  · linarith only [h0, h239, hlam]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h156, h174, h2, h4, hlam, p184_1, p219_2]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h153, h4, hlam, p184_1, p219_2]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h152, hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h174, hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h178, hlam, p219_1]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h180, hlam, p219_1]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h153, hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h175, hlam, p219_0]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h179, hlam, p219_1]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [h175, h178, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p184_1, p219_1, u0elo1]
                                                · have p219_0 := h219c.1
                                                  have p219_1 := h219c.2.1
                                                  have p219_2 := h219c.2.2.1
                                                  have p219_3 := h219c.2.2.2
                                                  linarith only [hlam, p219_0]
                                          · linarith only [h155, h214, hlam]
                                        · linarith only [h153, h213, hlam]
                                      · linarith only [h212, h3, hlam]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h1, hlam, p184_1]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h1, h152, h178, hc34, hlam, hphi, ht0b, ht45, ht5b, p184_1, u0elo0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      rcases p184_3 (m.d 0 1) (by simp) with h261 | h261
                                      · rcases p184_3 (m.d 0 2) (by simp) with h262 | h262
                                        · linarith only [h262, h4, hlam]
                                        · linarith only [h152, h262, hlam]
                                      · linarith only [h2, h261, hlam]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      rcases p184_3 (m.d 0 1) (by simp) with h266 | h266
                                      · rcases p184_3 (m.d 0 2) (by simp) with h267 | h267
                                        · linarith only [h267, h4, hlam]
                                        · linarith only [h153, h267, hlam]
                                      · linarith only [h266, h3, hlam]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h2, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h152, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h154, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h156, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h3, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h153, hlam, p184_1]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h155, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h156, h174, h178, h2, hc34, hlam, hphi, p184_1, u4elo4]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [hlam, p184_0]
                              · linarith only [h155, h179, h4, hlam]
                            · linarith only [h178, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                        · linarith only [h153, h174, h175, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h152, h174, h4, hc12, hc23, hlam, hphi]
                · linarith only [h153, h155, h4, hlam]
              · linarith only [h152, h154, h4, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h287 | h287
              · rcases m.htr 0 3 5 (by decide) (by decide) with h288 | h288
                · rcases m.htr 0 4 5 (by decide) (by decide) with h289 | h289
                  · linarith only [h152, h153, h289, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
                    · linarith only [h0, h291, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                        · linarith only [h0, h153, h294, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h296 | h296
                          · linarith only [h2, h289, h296, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h298 | h298
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h299 | h299
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h300 | h300
                                · linarith only [h0, h289, h293, h300, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h152, h153, h298, h300, hc34, hlam, hphi, u4elo4]
                              · linarith only [h0, h288, h293, h298, h299, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h298, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h152, h293, h4, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h306 | h306
                  · linarith only [h152, h288, h306, h4, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h308 | h308
                    · linarith only [h0, h308, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h310 | h310
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
                        · linarith only [h0, h153, h311, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h313 | h313
                          · linarith only [h306, h313, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h316 | h316
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h317 | h317
                                · linarith only [h0, h288, h306, h310, h317, h4, hlam]
                                · linarith only [h0, h288, h310, h315, h316, h317, h4, hc34, hlam, hphi, u4elo4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h320 | h320
                                · linarith only [h0, h310, h320, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h0, h153, h310, h315, h320, hc34, hlam, hphi, u4elo4]
                            · linarith only [h315, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h152, h310, h4, hc12, hc23, hlam, hphi]
              · linarith only [h152, h287, h4, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h326 | h326
            · rcases m.htr 0 3 4 (by decide) (by decide) with h327 | h327
              · rcases m.htr 0 3 5 (by decide) (by decide) with h328 | h328
                · rcases m.htr 0 4 5 (by decide) (by decide) with h329 | h329
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
                    · linarith only [h0, h152, h330, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h332 | h332
                      · linarith only [h0, h152, h332, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h335 | h335
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h337 | h337
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h338 | h338
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h339 | h339
                                  · rcases h0bigk with h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [hlam, p340_0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h0, h334, hc25, hlam, hphi, ht0b, ht5b, p340_1, u0elo0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h327, hc34, hlam, hphi, ht0b, ht45, ht5b, p340_1, u0elo0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h2, h332, h334, h337, hc35, hlam, hphi, ht0b, ht5b, p340_1, u0elo0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      rcases p340_3 (m.d 0 1) (by simp) with h345 | h345
                                      · rcases p340_3 (m.d 0 2) (by simp) with h346 | h346
                                        · linarith only [h0, h346, hlam]
                                        · linarith only [h326, h346, hlam]
                                      · linarith only [h3, h345, hlam]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h0, hlam, p340_0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [hlam, p340_0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h4, hlam, p340_0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h152, hlam, p340_1]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h152, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p340_1, u4elo2]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h1, hlam, p340_1]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h0, h334, hc25, hlam, hphi, ht0b, ht5b, p340_1, u0elo2]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [hlam, p340_0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h2, h332, h334, h337, h339, hc45, hlam, hphi, ht0b, ht5b, p340_1, u0elo2]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      rcases p340_3 (m.d 0 1) (by simp) with h359 | h359
                                      · rcases p340_3 (m.d 0 2) (by simp) with h360 | h360
                                        · linarith only [h360, h4, hlam]
                                        · linarith only [h326, h360, hlam]
                                      · linarith only [h3, h359, hlam]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h2, hlam, p340_0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h0, h334, h337, h339, hc45, hlam, hphi, ht0b, ht5b, p340_1, u0elo3]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h327, hlam, p340_0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [hlam, p340_0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      rcases p340_3 (m.d 0 1) (by simp) with h368 | h368
                                      · rcases p340_3 (m.d 0 2) (by simp) with h369 | h369
                                        · linarith only [h152, h369, hlam]
                                        · linarith only [h326, h369, hlam]
                                      · linarith only [h3, h368, hlam]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h3, hlam, p340_0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h326, hlam, p340_1]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h328, hlam, p340_0]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [h329, hlam, p340_1]
                                    · have p340_0 := h340c.1
                                      have p340_1 := h340c.2.1
                                      have p340_2 := h340c.2.2.1
                                      have p340_3 := h340c.2.2.2
                                      linarith only [hlam, p340_0]
                                  · linarith only [h152, h329, h339, hc34, hlam, hphi, u4elo2]
                                · linarith only [h152, h2, h3, h332, h334, h335, h338, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h1, h152, h328, h336, h337, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h0, h334, h336, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h329, h335, hc14, hlam, hphi, u4elo0]
                        · linarith only [h152, h326, h334, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h152, h326, h329, hlam]
                · linarith only [h326, h328, h4, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h386 | h386
                · rcases m.htr 0 4 5 (by decide) (by decide) with h387 | h387
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h388 | h388
                    · linarith only [h0, h327, h388, h4, hc23, hlam, hphi, ht34, u4elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
                      · linarith only [h0, h152, h327, h390, h4, hc04, hlam, hphi, u4elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h392 | h392
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h393 | h393
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h395 | h395
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h396 | h396
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h397 | h397
                                  · rcases h0bigk with h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, h392, h395, h397, hc45, hlam, hphi, ht0b, ht5b, p398_1, u0elo0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, h392, h395, h397, h4, hc45, hlam, hphi, ht0b, ht5b, p398_1, u0elo0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, h327, h392, h395, h397, h4, hc45, hlam, hphi, ht0b, ht5b, p398_1, u0elo0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      rcases p398_3 (m.d 0 1) (by simp) with h403 | h403
                                      · rcases p398_3 (m.d 0 2) (by simp) with h404 | h404
                                        · linarith only [h0, h404, hlam]
                                        · linarith only [h326, h404, hlam]
                                      · linarith only [h3, h403, hlam]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h4, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h152, hlam, p398_1]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h327, h394, h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p398_1, u4elo2]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h1, hlam, p398_1]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h327, h394, hc02, hlam, hphi, ht23, ht34, p398_1, u4elo2]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h327, hlam, p398_1]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h326, h327, h394, h395, h397, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p398_1, u4elo2]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h2, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, h392, h395, h397, hc45, hlam, hphi, ht0b, ht5b, p398_1, u0elo3]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h327, h394, hc03, hlam, hphi, ht34, p398_1, u4elo2]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      rcases p398_3 (m.d 0 1) (by simp) with h422 | h422
                                      · rcases p398_3 (m.d 0 2) (by simp) with h423 | h423
                                        · linarith only [h152, h423, hlam]
                                        · linarith only [h326, h423, hlam]
                                      · linarith only [h3, h422, hlam]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h3, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h326, hlam, p398_1]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h386, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h387, hlam, p398_1]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [hlam, p398_0]
                                  · linarith only [h327, h397, hc03, hlam, hphi, ht34, u4elo4]
                                · linarith only [h152, h396, hc02, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h1, h327, h388, h392, h394, h395, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h394, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h152, h387, h390, h392, h393, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                        · linarith only [h326, h327, h392, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h326, h327, h387, h4, hlam]
                · linarith only [h326, h386, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h440 | h440
              · rcases m.htr 0 3 5 (by decide) (by decide) with h441 | h441
                · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
                    · linarith only [h0, h4, h443, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                      · linarith only [h0, h152, h445, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
                        · linarith only [h0, h326, h447, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h451 | h451
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h453 | h453
                                  · rcases h0bigk with h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      rcases p454_3 (m.d 0 1) (by simp) with h456 | h456
                                      · rcases p454_3 (m.d 0 2) (by simp) with h457 | h457
                                        · linarith only [h0, h457, hlam]
                                        · rcases p454_3 (m.d 0 3) (by simp) with h459 | h459
                                          · linarith only [h1, h459, hlam]
                                          · linarith only [h4, h459, hlam]
                                      · linarith only [h0, h456, hlam]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h440, h453, hc45, hlam, hphi, ht0b, ht5b, p454_1, u0elo0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h440, h453, hc45, hlam, hphi, ht0b, ht5b, p454_1, u0elo0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      rcases p454_3 (m.d 0 1) (by simp) with h465 | h465
                                      · rcases p454_3 (m.d 0 2) (by simp) with h466 | h466
                                        · linarith only [h0, h466, hlam]
                                        · rcases p454_3 (m.d 0 3) (by simp) with h468 | h468
                                          · linarith only [h1, h468, hlam]
                                          · linarith only [h441, h468, hlam]
                                      · linarith only [h3, h465, hlam]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h0, hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h4, hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h152, hlam, p454_1]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h326, hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h1, hlam, p454_1]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      rcases p454_3 (m.d 0 1) (by simp) with h478 | h478
                                      · rcases p454_3 (m.d 0 2) (by simp) with h479 | h479
                                        · linarith only [h4, h479, hlam]
                                        · rcases p454_3 (m.d 0 3) (by simp) with h481 | h481
                                          · rcases p454_3 (m.d 0 4) (by simp) with h482 | h482
                                            · linarith only [h440, h482, hlam]
                                            · linarith only [h152, h482, hlam]
                                          · linarith only [h4, h481, hlam]
                                      · linarith only [h0, h478, hlam]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h440, h453, hc45, hlam, hphi, ht0b, ht5b, p454_1, u0elo2]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      rcases p454_3 (m.d 0 1) (by simp) with h489 | h489
                                      · rcases p454_3 (m.d 0 2) (by simp) with h490 | h490
                                        · linarith only [h4, h490, hlam]
                                        · rcases p454_3 (m.d 0 3) (by simp) with h492 | h492
                                          · rcases p454_3 (m.d 0 4) (by simp) with h493 | h493
                                            · linarith only [h440, h493, hlam]
                                            · linarith only [h442, h493, hlam]
                                          · linarith only [h441, h492, hlam]
                                      · linarith only [h3, h489, hlam]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h2, hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, p454_1, u4elo0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h440, hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h0, h152, h326, hc12, hlam, hphi, ht23, ht34, p454_1, u4elo2]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h3, hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h0, h326, h452, hc12, hlam, hphi, ht23, ht34, p454_1, u4elo2]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h441, hlam, p454_0]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [h442, hlam, p454_1]
                                    · have p454_0 := h454c.1
                                      have p454_1 := h454c.2.1
                                      have p454_2 := h454c.2.2.1
                                      have p454_3 := h454c.2.2.2
                                      linarith only [hlam, p454_0]
                                  · linarith only [h449, h453, hc34, hlam, hphi, u4elo1]
                                · linarith only [h0, h152, h3, h449, h452, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h4, h441, h451, hlam]
                            · linarith only [h0, h4, h450, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h152, h442, h449, hc14, hlam, hphi, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h513 | h513
                    · linarith only [h0, h4, h513, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h515 | h515
                      · linarith only [h0, h152, h515, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h517 | h517
                        · linarith only [h0, h326, h517, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h519 | h519
                          · linarith only [h152, h442, h519, hc02, hlam, hphi, ht23, ht34, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h521 | h521
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h522 | h522
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h523 | h523
                                · linarith only [h0, h152, h442, h523, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h0, h152, h523, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h0, h152, h441, h521, h522, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h0, h4, h521, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
                  · linarith only [h440, h441, h528, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h530 | h530
                    · linarith only [h0, h4, h530, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h532 | h532
                      · linarith only [h0, h152, h532, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h534 | h534
                        · linarith only [h0, h326, h534, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h536 | h536
                          · linarith only [h2, h528, h536, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h538 | h538
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h539 | h539
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h540 | h540
                                · linarith only [h528, h540, hc04, hlam, hphi, u4elo2]
                                · linarith only [h0, h152, h540, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h543 | h543
                                · linarith only [h0, h152, h528, h543, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h0, h152, h543, hc12, hlam, hphi, ht23, ht34, u4elo4]
                            · linarith only [h0, h4, h440, h538, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h547 | h547
                · rcases m.htr 0 4 5 (by decide) (by decide) with h548 | h548
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h549 | h549
                    · linarith only [h0, h4, h549, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h551 | h551
                      · linarith only [h0, h152, h551, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h553 | h553
                        · linarith only [h0, h326, h553, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h555 | h555
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h556 | h556
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h557 | h557
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h558 | h558
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h559 | h559
                                  · rcases h0bigk with h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [hlam, p560_0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      rcases p560_3 (m.d 0 1) (by simp) with h562 | h562
                                      · rcases p560_3 (m.d 0 2) (by simp) with h563 | h563
                                        · linarith only [h0, h563, hlam]
                                        · rcases p560_3 (m.d 0 3) (by simp) with h565 | h565
                                          · linarith only [h1, h565, hlam]
                                          · linarith only [h4, h565, hlam]
                                      · linarith only [h0, h562, hlam]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h547, h559, hc45, hlam, hphi, ht0b, ht5b, p560_1, u0elo0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h440, h547, h559, hc45, hlam, hphi, ht0b, ht5b, p560_1, u0elo0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      rcases p560_3 (m.d 0 1) (by simp) with h571 | h571
                                      · rcases p560_3 (m.d 0 2) (by simp) with h572 | h572
                                        · linarith only [h0, h572, hlam]
                                        · rcases p560_3 (m.d 0 3) (by simp) with h574 | h574
                                          · linarith only [h1, h574, hlam]
                                          · linarith only [h547, h574, hlam]
                                      · linarith only [h3, h571, hlam]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h0, hlam, p560_0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [hlam, p560_0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h4, hlam, p560_0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h152, hlam, p560_1]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h326, hlam, p560_0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h1, hlam, p560_1]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h0, h440, h556, hc12, hc23, hlam, hphi, p560_1]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [hlam, p560_0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h440, hlam, p560_1]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h0, h326, h440, h556, hc12, hlam, hphi, ht23, ht34, p560_1, u4elo2]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h2, hlam, p560_0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, p560_1, u4elo0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h440, h556, hc03, hlam, hphi, ht34, p560_1, u4elo2]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [hlam, p560_0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h0, h326, h440, h556, hc12, hlam, hphi, ht23, ht34, p560_1, u4elo2]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h3, hlam, p560_0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h0, h440, h547, h556, hc12, hlam, hphi, ht23, ht34, p560_1, u4elo2]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h547, hlam, p560_0]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [h548, hlam, p560_1]
                                    · have p560_0 := h560c.1
                                      have p560_1 := h560c.2.1
                                      have p560_2 := h560c.2.2.1
                                      have p560_3 := h560c.2.2.2
                                      linarith only [hlam, p560_0]
                                  · linarith only [h440, h547, h555, h559, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h3, h440, h547, h555, h556, h558, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                              · linarith only [h440, h547, h556, h557, hc23, hlam, hphi, ht34, u4elo2]
                            · linarith only [h0, h4, h556, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h152, h548, h555, hc14, hlam, hphi, u4elo2]
                  · linarith only [h440, h547, h548, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h604 | h604
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h605 | h605
                    · linarith only [h0, h4, h605, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h607 | h607
                      · linarith only [h0, h152, h607, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h609 | h609
                        · linarith only [h0, h326, h609, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h611 | h611
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h612 | h612
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h613 | h613
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h614 | h614
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h615 | h615
                                  · rcases h0bigk with h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      rcases p616_3 (m.d 0 1) (by simp) with h618 | h618
                                      · rcases p616_3 (m.d 0 2) (by simp) with h619 | h619
                                        · linarith only [h0, h619, hlam]
                                        · rcases p616_3 (m.d 0 3) (by simp) with h621 | h621
                                          · linarith only [h1, h621, hlam]
                                          · linarith only [h4, h621, hlam]
                                      · linarith only [h0, h618, hlam]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      rcases p616_3 (m.d 0 1) (by simp) with h625 | h625
                                      · rcases p616_3 (m.d 0 2) (by simp) with h626 | h626
                                        · linarith only [h0, h626, hlam]
                                        · rcases p616_3 (m.d 0 3) (by simp) with h628 | h628
                                          · linarith only [h1, h628, hlam]
                                          · rcases p616_3 (m.d 0 4) (by simp) with h630 | h630
                                            · linarith only [h2, h630, hlam]
                                            · linarith only [h440, h630, hlam]
                                      · linarith only [h1, h625, hlam]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h2, h611, hc45, hlam, hphi, ht0b, ht5b, p616_1, u0elo0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      rcases p616_3 (m.d 0 1) (by simp) with h635 | h635
                                      · rcases p616_3 (m.d 0 2) (by simp) with h636 | h636
                                        · linarith only [h0, h636, hlam]
                                        · rcases p616_3 (m.d 0 3) (by simp) with h638 | h638
                                          · linarith only [h1, h638, hlam]
                                          · rcases p616_3 (m.d 0 4) (by simp) with h640 | h640
                                            · linarith only [h2, h640, hlam]
                                            · linarith only [h604, h640, hlam]
                                      · linarith only [h3, h635, hlam]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h0, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h4, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h152, hlam, p616_1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h326, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h1, hlam, p616_1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h0, h547, h612, h615, hc12, hc23, hlam, hphi, p616_1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h440, hlam, p616_1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h547, hlam, p616_1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h2, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, p616_1, u4elo0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h152, hc03, hlam, hphi, ht34, p616_1, u4elo2]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h1, h152, h547, h605, hc12, hlam, hphi, ht23, ht34, p616_1, u4elo2]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h3, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h0, h326, h614, hc12, hlam, hphi, ht23, ht34, p616_1, u4elo2]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h1, h547, h605, h613, h614, hc12, hlam, hphi, ht23, ht34, p616_1, u4elo2]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h604, hlam, p616_1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hlam, p616_0]
                                  · linarith only [h1, h440, h605, h615, hc12, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h2, h611, h614, hc24, hlam, hphi, u4elo0]
                              · linarith only [h1, h440, h605, h612, h613, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h4, h612, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h152, h604, h611, hc14, hlam, hphi, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h669 | h669
                    · linarith only [h0, h4, h669, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h671 | h671
                      · linarith only [h0, h152, h671, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h673 | h673
                        · linarith only [h0, h326, h673, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h675 | h675
                          · linarith only [h0, h4, h440, h604, h675, hc12, hlam, hphi, ht23, ht34, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h677 | h677
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h678 | h678
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h679 | h679
                                · linarith only [h0, h4, h440, h604, h679, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h0, h152, h679, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h0, h4, h440, h677, h678, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h4, h677, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h684 | h684
        · rcases m.htr 0 2 4 (by decide) (by decide) with h685 | h685
          · rcases m.htr 0 2 5 (by decide) (by decide) with h686 | h686
            · linarith only [h0, h3, h686, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h688 | h688
              · rcases m.htr 0 3 5 (by decide) (by decide) with h689 | h689
                · linarith only [h1, h3, h689, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h691 | h691
                  · linarith only [h2, h3, h691, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h693 | h693
                    · linarith only [h0, h3, h691, h693, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h3, h684, h691, h693, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h696 | h696
                · linarith only [h2, h3, h688, h696, hc14, hlam, hphi, u4elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h698 | h698
                  · linarith only [h2, h3, h698, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h700 | h700
                    · linarith only [h0, h3, h698, h700, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h3, h684, h698, h700, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h684, h685, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h704 | h704
          · rcases m.htr 0 2 5 (by decide) (by decide) with h705 | h705
            · linarith only [h1, h3, h684, h705, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h707 | h707
              · rcases m.htr 0 3 5 (by decide) (by decide) with h708 | h708
                · linarith only [h1, h3, h708, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h710 | h710
                  · linarith only [h2, h3, h710, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h712 | h712
                    · linarith only [h0, h684, h712, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h714 | h714
                      · linarith only [h0, h3, h710, h714, hc24, hlam, hphi, u4elo4]
                      · linarith only [h684, h704, h714, hc12, hc23, hlam, hphi]
              · linarith only [h684, h704, h707, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h718 | h718
            · linarith only [h1, h3, h704, h718, hc13, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h720 | h720
              · rcases m.htr 0 3 5 (by decide) (by decide) with h721 | h721
                · linarith only [h1, h3, h721, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h723 | h723
                  · linarith only [h2, h3, h723, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h725 | h725
                    · linarith only [h0, h704, h723, h725, hc23, hlam, hphi, ht34, u4elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h727 | h727
                      · linarith only [h1, h3, h723, h725, h727, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h729 | h729
                        · linarith only [h1, h3, h718, h725, h729, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h731 | h731
                          · linarith only [h704, h723, h731, hc02, hlam, hphi, ht23, ht34, u4elo1]
                          · linarith only [h1, h3, h725, h731, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h734 | h734
                · linarith only [h1, h3, h734, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h736 | h736
                  · linarith only [h2, h3, h736, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h738 | h738
                    · linarith only [h0, h684, h738, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h740 | h740
                      · linarith only [h0, h704, h740, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h742 | h742
                        · linarith only [h0, h718, h742, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h744 | h744
                          · linarith only [h2, h720, h736, h744, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h3, h744, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h748 | h748
    · rcases m.htr 0 1 5 (by decide) (by decide) with h749 | h749
      · rcases m.htr 0 2 3 (by decide) (by decide) with h750 | h750
        · linarith only [h0, h1, h750, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h752 | h752
          · rcases m.htr 0 2 5 (by decide) (by decide) with h753 | h753
            · rcases m.htr 0 3 4 (by decide) (by decide) with h754 | h754
              · rcases m.htr 0 3 5 (by decide) (by decide) with h755 | h755
                · rcases m.htr 0 4 5 (by decide) (by decide) with h756 | h756
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h757 | h757
                    · linarith only [h0, h750, h757, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h759 | h759
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h760 | h760
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h761 | h761
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h762 | h762
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h763 | h763
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h764 | h764
                                · linarith only [h0, h1, h757, h759, h764, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h748, h761, h764, hc24, hlam, hphi, u4elo0]
                              · linarith only [h0, h1, h757, h763, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h757, h762, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h756, h761, hc14, hlam, hphi, u4elo0]
                        · linarith only [h0, h753, h759, h760, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h752, h757, h759, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
                    · linarith only [h0, h750, h772, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h774 | h774
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h775 | h775
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h776 | h776
                          · linarith only [h756, h776, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h778 | h778
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h779 | h779
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h780 | h780
                                · linarith only [h748, h756, h774, h780, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h782 | h782
                                  · linarith only [h748, h756, h774, h778, h782, hlam]
                                  · rcases h0bigk with h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h0, h1, h772, h775, h778, h780, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p784_1]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h1, hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      rcases p784_3 (m.d 0 1) (by simp) with h788 | h788
                                      · rcases p784_3 (m.d 0 2) (by simp) with h789 | h789
                                        · linarith only [h0, h789, hlam]
                                        · linarith only [h752, h789, hlam]
                                      · linarith only [h748, h788, hlam]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      rcases p784_3 (m.d 0 1) (by simp) with h793 | h793
                                      · rcases p784_3 (m.d 0 2) (by simp) with h794 | h794
                                        · linarith only [h0, h794, hlam]
                                        · linarith only [h753, h794, hlam]
                                      · linarith only [h749, h793, hlam]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h0, hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h750, hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      rcases p784_3 (m.d 0 1) (by simp) with h801 | h801
                                      · rcases p784_3 (m.d 0 2) (by simp) with h802 | h802
                                        · rcases p784_3 (m.d 0 3) (by simp) with h803 | h803
                                          · rcases p784_3 (m.d 0 4) (by simp) with h804 | h804
                                            · linarith only [h752, h804, hlam]
                                            · rcases p784_3 (m.d 0 5) (by simp) with h806 | h806
                                              · linarith only [h753, h806, hlam]
                                              · linarith only [h756, h806, hlam]
                                          · linarith only [h754, h803, hlam]
                                        · linarith only [h752, h802, hlam]
                                      · linarith only [h748, h801, hlam]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      rcases p784_3 (m.d 0 1) (by simp) with h812 | h812
                                      · rcases p784_3 (m.d 0 2) (by simp) with h813 | h813
                                        · rcases p784_3 (m.d 0 3) (by simp) with h814 | h814
                                          · rcases p784_3 (m.d 0 4) (by simp) with h815 | h815
                                            · linarith only [h752, h815, hlam]
                                            · rcases p784_3 (m.d 0 5) (by simp) with h817 | h817
                                              · linarith only [h753, h817, hlam]
                                              · rcases h2bigk with h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h775, h778, h780, hc34, hlam, hphi, ht0b, ht45, ht5b, p819_1, u0elo1]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h750, hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  rcases p819_3 (m.d 0 2) (by simp) with h823 | h823
                                                  · rcases p819_3 (m.d 1 2) (by simp) with h824 | h824
                                                    · linarith only [h0, h824, hlam]
                                                    · linarith only [h774, h824, hlam]
                                                  · linarith only [h823, hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  rcases p819_3 (m.d 0 2) (by simp) with h828 | h828
                                                  · rcases p819_3 (m.d 1 2) (by simp) with h829 | h829
                                                    · linarith only [h0, h829, hlam]
                                                    · linarith only [h775, h829, hlam]
                                                  · linarith only [h828, hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h0, hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h772, hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h0, h1, h772, h778, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p819_1]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h0, h1, h772, h778, h780, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p819_1]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h748, h756, h774, h778, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p784_1, p819_1]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  rcases p819_3 (m.d 0 2) (by simp) with h839 | h839
                                                  · linarith only [h750, h839, hlam]
                                                  · linarith only [h0, h839, hlam]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h0, h1, h748, h756, h772, h774, hlam, p784_1, p819_2]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h0, h1, h753, h772, hlam, p784_1, p819_2]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h752, hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h774, hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h778, hlam, p819_1]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h780, hlam, p819_1]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h753, hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h775, hlam, p819_0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h779, hlam, p819_1]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [h0, h749, h775, h778, hc34, hlam, hphi, ht0b, ht45, ht5b, p784_1, p819_1, u0elo0]
                                                · have p819_0 := h819c.1
                                                  have p819_1 := h819c.2.1
                                                  have p819_2 := h819c.2.2.1
                                                  have p819_3 := h819c.2.2.2
                                                  linarith only [hlam, p819_0]
                                          · linarith only [h755, h814, hlam]
                                        · linarith only [h753, h813, hlam]
                                      · linarith only [h749, h812, hlam]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p784_1, u0elo2]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h752, h778, hc34, hlam, hphi, ht0b, ht45, ht5b, p784_1, u0elo2]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      rcases p784_3 (m.d 0 1) (by simp) with h861 | h861
                                      · linarith only [h1, h861, hlam]
                                      · linarith only [h748, h861, hlam]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      rcases p784_3 (m.d 0 1) (by simp) with h864 | h864
                                      · linarith only [h1, h864, hlam]
                                      · linarith only [h749, h864, hlam]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h748, hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h752, hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h754, hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h756, hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h749, hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h753, hlam, p784_1]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h755, hlam, p784_0]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [h748, h756, h774, h778, hc34, hlam, hphi, p784_1, u4elo4]
                                    · have p784_0 := h784c.1
                                      have p784_1 := h784c.2.1
                                      have p784_2 := h784c.2.2.1
                                      have p784_3 := h784c.2.2.2
                                      linarith only [hlam, p784_0]
                              · linarith only [h0, h1, h772, h779, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h772, h774, h778, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h753, h774, h775, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h752, h772, h774, hc12, hc23, hlam, hphi]
                · linarith only [h1, h749, h755, hlam]
              · linarith only [h0, h1, h754, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h883 | h883
              · rcases m.htr 0 3 5 (by decide) (by decide) with h884 | h884
                · rcases m.htr 0 4 5 (by decide) (by decide) with h885 | h885
                  · linarith only [h752, h753, h885, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h887 | h887
                    · linarith only [h0, h750, h887, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h889 | h889
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h890 | h890
                        · linarith only [h0, h753, h890, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h892 | h892
                          · linarith only [h885, h892, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h894 | h894
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h895 | h895
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h896 | h896
                                · linarith only [h0, h753, h885, h889, h896, hlam]
                                · linarith only [h0, h753, h889, h894, h896, hc34, hlam, hphi, u4elo4]
                              · linarith only [h0, h1, h884, h887, h889, h894, h895, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                            · linarith only [h1, h749, h887, h890, h894, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h752, h753, h889, hc12, hc25, hlam, hphi]
                · linarith only [h1, h749, h884, hlam]
              · linarith only [h0, h1, h883, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h904 | h904
            · rcases m.htr 0 3 4 (by decide) (by decide) with h905 | h905
              · rcases m.htr 0 3 5 (by decide) (by decide) with h906 | h906
                · rcases m.htr 0 4 5 (by decide) (by decide) with h907 | h907
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h908 | h908
                    · linarith only [h0, h750, h908, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h910 | h910
                      · linarith only [h0, h752, h910, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h912 | h912
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h913 | h913
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h914 | h914
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h915 | h915
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h916 | h916
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h917 | h917
                                  · rcases h0bigk with h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h0, h1, h908, h912, h915, h917, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p918_1]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h1, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h0, h1, h752, h908, h912, h915, h917, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p918_1]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      rcases p918_3 (m.d 0 1) (by simp) with h923 | h923
                                      · rcases p918_3 (m.d 0 2) (by simp) with h924 | h924
                                        · linarith only [h0, h924, hlam]
                                        · linarith only [h904, h924, hlam]
                                      · linarith only [h749, h923, hlam]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h0, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h750, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h752, hlam, p918_1]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h752, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p918_1, u4elo2]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p918_1, u0elo2]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h0, h912, h915, h917, hc45, hlam, hphi, ht0b, ht5b, p918_1, u0elo2]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h0, h752, h912, h915, h917, hc45, hlam, hphi, ht0b, ht5b, p918_1, u0elo2]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      rcases p918_3 (m.d 0 1) (by simp) with h937 | h937
                                      · linarith only [h1, h937, hlam]
                                      · linarith only [h749, h937, hlam]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h748, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h0, h912, h915, h917, hc45, hlam, hphi, ht0b, ht5b, p918_1, u0elo3]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h905, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      rcases p918_3 (m.d 0 1) (by simp) with h944 | h944
                                      · rcases p918_3 (m.d 0 2) (by simp) with h945 | h945
                                        · linarith only [h752, h945, hlam]
                                        · linarith only [h904, h945, hlam]
                                      · linarith only [h749, h944, hlam]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h749, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h904, hlam, p918_1]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h906, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h907, hlam, p918_1]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [hlam, p918_0]
                                  · linarith only [h907, h917, hc34, hlam, hphi, u4elo0]
                                · linarith only [h0, h749, h752, h912, h913, h916, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                              · linarith only [h1, h748, h908, h913, h915, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h748, h908, h910, h912, h914, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h748, h907, h910, h912, h913, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h1, h904, h908, h912, hc12, hc23, hlam, hphi]
                  · linarith only [h752, h904, h907, hlam]
                · linarith only [h0, h1, h904, h906, hlam]
              · linarith only [h0, h1, h905, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h963 | h963
              · rcases m.htr 0 3 5 (by decide) (by decide) with h964 | h964
                · rcases m.htr 0 4 5 (by decide) (by decide) with h965 | h965
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h966 | h966
                    · linarith only [h0, h750, h966, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h968 | h968
                      · linarith only [h0, h752, h968, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h970 | h970
                        · linarith only [h0, h904, h970, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h972 | h972
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h973 | h973
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h974 | h974
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h975 | h975
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h976 | h976
                                  · rcases h0bigk with h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h1, h966, hc02, hc23, hlam, hphi, p977_1]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h1, hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h0, h1, h904, h965, h966, hc12, hc23, hlam, hphi, p977_1]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h0, h1, h904, h966, hc12, hc23, hlam, hphi, p977_1]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h0, hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h750, hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h752, hlam, p977_1]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h904, hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p977_1, u0elo2]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      rcases p977_3 (m.d 0 1) (by simp) with h989 | h989
                                      · linarith only [h1, h989, hlam]
                                      · linarith only [h0, h989, hlam]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h748, h972, hc45, hlam, hphi, ht0b, ht5b, p977_1, u0elo2]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      rcases p977_3 (m.d 0 1) (by simp) with h994 | h994
                                      · linarith only [h1, h994, hlam]
                                      · linarith only [h749, h994, hlam]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h748, hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, p977_1, u4elo0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h963, hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h0, h752, h904, hc12, hlam, hphi, ht23, ht34, p977_1, u4elo2]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h749, hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h0, h1, h749, h966, hc12, hc23, hlam, hphi, p977_1]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h964, hlam, p977_0]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [h965, hlam, p977_1]
                                    · have p977_0 := h977c.1
                                      have p977_1 := h977c.2.1
                                      have p977_2 := h977c.2.2.1
                                      have p977_3 := h977c.2.2.2
                                      linarith only [hlam, p977_0]
                                  · linarith only [h972, h976, hc34, hlam, hphi, u4elo1]
                                · linarith only [h1, h748, h752, h966, h972, h975, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h1, h964, h965, h966, h974, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                            · linarith only [h1, h748, h966, h972, h973, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h752, h965, h972, hc14, hlam, hphi, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1012 | h1012
                    · linarith only [h0, h1012, h752, h965, hc23, hlam, hphi, ht34, u4elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1014 | h1014
                      · linarith only [h0, h1014, h752, h965, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1016 | h1016
                        · linarith only [h0, h1016, h904, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1018 | h1018
                          · linarith only [h1018, h748, h752, h965, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1020 | h1020
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1021 | h1021
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1022 | h1022
                                · linarith only [h0, h1022, h752, h965, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h0, h1022, h752, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h1, h1012, h1021, h964, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1, h1012, h1014, h1018, h1020, h749, h963, hc12, hlam, hphi, ht23, ht34, u4elo0]
                · linarith only [h1, h749, h964, hlam]
              · linarith only [h0, h1, h963, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1029 | h1029
        · linarith only [h0, h1, h1029, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1031 | h1031
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1032 | h1032
            · linarith only [h0, h1032, h749, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1034 | h1034
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1035 | h1035
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1036 | h1036
                  · linarith only [h0, h1031, h1036, h749, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1038 | h1038
                    · linarith only [h0, h1029, h1038, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1040 | h1040
                      · linarith only [h0, h1036, h1040, h749, hc24, hlam, hphi, u4elo4]
                      · linarith only [h1031, h1032, h1040, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1043 | h1043
                  · linarith only [h1, h1035, h1043, h748, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1045 | h1045
                    · linarith only [h0, h1029, h1045, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1047 | h1047
                      · linarith only [h0, h1, h1035, h1043, h1047, hc24, hlam, hphi, u4elo4]
                      · linarith only [h1031, h1032, h1047, hc12, hc25, hlam, hphi]
              · linarith only [h1, h1034, h748, hc14, hlam, hphi, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1051 | h1051
            · linarith only [h0, h1031, h1051, h749, hc12, hlam, hphi, ht23, ht34, u4elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1053 | h1053
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1054 | h1054
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1055 | h1055
                  · linarith only [h1055, h748, h749, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1057 | h1057
                    · linarith only [h0, h1029, h1057, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1059 | h1059
                      · linarith only [h0, h1055, h1059, h749, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1061 | h1061
                        · linarith only [h1051, h1059, h1061, h748, h749, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1063 | h1063
                          · linarith only [h1055, h1063, h748, h749, hlam]
                          · linarith only [h1059, h1063, h748, h749, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1066 | h1066
                  · linarith only [h1066, h748, h749, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1068 | h1068
                    · linarith only [h0, h1, h1029, h1031, h1068, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1070 | h1070
                      · linarith only [h0, h1031, h1066, h1070, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1072 | h1072
                        · linarith only [h1, h1051, h1054, h1070, h1072, h748, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1074 | h1074
                          · linarith only [h1, h1054, h1066, h1074, h748, hlam]
                          · linarith only [h1070, h1074, h748, h749, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · linarith only [h0, h1, h1053, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · linarith only [h0, h748, hc12, hlam, hphi, ht23, ht34, u4elo1]

end R2N4
