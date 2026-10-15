import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3458000 in
set_option maxHeartbeats 3458000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
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
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                                · linarith only [h0, h10, h16, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h16, h7, hc23, hlam, hphi, u3elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                                · linarith only [h0, h10, h19, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h19, h7, hc23, hlam, hphi, u3elo0]
                            · linarith only [h14, h8, hc13, hlam, hphi, u3elo0]
                          · linarith only [h10, h13, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h12, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                              · linarith only [h2, h32, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                                · linarith only [h0, h27, h34, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h30, h34, hc23, hlam, hphi, u3elo1]
                            · linarith only [h31, h8, hc13, hlam, hphi, u3elo0]
                          · linarith only [h27, h30, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h29, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h27, h28, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h27, h4, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
                  · linarith only [h42, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                            · linarith only [h1, h48, h8, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                              · linarith only [h2, h42, h50, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                                · linarith only [h0, h44, h52, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h1, h47, h52, h8, hc23, hlam, hphi, u3elo4]
                          · linarith only [h47, h7, h8, hc13, hlam, hphi, u3elo4]
                        · linarith only [h46, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h44, h45, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h4, h44, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h59 | h59
                · rcases m.htr 0 4 5 (by decide) (by decide) with h60 | h60
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h64 | h64
                          · linarith only [h64, h7, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h66 | h66
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                                · linarith only [h1, h61, h66, h68, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                                  · linarith only [h0, h62, h68, h70, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h1, h66, h7, h70, hc23, hlam, hphi, u3elo3]
                              · linarith only [h59, h60, h64, h67, h7, hc13, hlam, hphi, u3elo3]
                            · linarith only [h59, h61, h66, h7, hc23, hlam, hphi, u3elo3]
                        · linarith only [h6, h63, hc12, hlam, hphi, u2elo0]
                      · linarith only [h5, h61, h62, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h4, h61, hc12, hlam, hphi, u2elo0]
                  · linarith only [h59, h60, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
                          · linarith only [h7, h83, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                            · linarith only [h1, h59, h85, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                                · linarith only [h1, h7, h80, h88, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                                  · linarith only [h1, h59, h80, h90, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                                    · linarith only [h0, h81, h92, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h2, h87, h92, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h7, h79, h80, h83, h87, hc23, hlam, hphi, u3elo3]
                        · linarith only [h6, h82, hc12, hlam, hphi, u2elo0]
                      · linarith only [h5, h80, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h4, h80, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                          · linarith only [h1, h102, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
                            · linarith only [h1, h104, h59, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                              · linarith only [h106, h2, h79, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                                · linarith only [h1, h108, h7, h99, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                                  · linarith only [h1, h110, h59, h99, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
                                    · linarith only [h100, h112, h2, h79, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h114 | h114
                                      · linarith only [h114, h7, h79, hc03, hlam, hphi, u3elo3]
                                      · rcases h0bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [hlam, p116_0]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h0, h101, h112, hc24, hlam, hphi, ht0b, ht45, ht5b, p116_1, u0elo0]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          rcases p116_3 (m.d 0 1) (by simp) with h119 | h119
                                          · rcases p116_3 (m.d 0 2) (by simp) with h120 | h120
                                            · linarith only [h0, h120, hlam]
                                            · linarith only [h120, h4, hlam]
                                          · linarith only [h1, h119, hlam]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          rcases p116_3 (m.d 0 1) (by simp) with h124 | h124
                                          · rcases p116_3 (m.d 0 2) (by simp) with h125 | h125
                                            · linarith only [h0, h125, hlam]
                                            · linarith only [h125, h5, hlam]
                                          · linarith only [h124, h2, hlam]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          rcases p116_3 (m.d 0 1) (by simp) with h129 | h129
                                          · rcases p116_3 (m.d 0 2) (by simp) with h130 | h130
                                            · linarith only [h0, h130, hlam]
                                            · linarith only [h130, h6, hlam]
                                          · linarith only [h129, h3, hlam]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h0, hlam, p116_0]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [hlam, p116_0]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          rcases p116_3 (m.d 0 1) (by simp) with h136 | h136
                                          · rcases p116_3 (m.d 0 2) (by simp) with h137 | h137
                                            · rcases p116_3 (m.d 0 3) (by simp) with h138 | h138
                                              · linarith only [h138, h4, hlam]
                                              · rcases p116_3 (m.d 0 4) (by simp) with h140 | h140
                                                · linarith only [h140, h5, hlam]
                                                · linarith only [h140, h7, hlam]
                                            · linarith only [h137, h4, hlam]
                                          · linarith only [h1, h136, hlam]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          rcases p116_3 (m.d 0 1) (by simp) with h145 | h145
                                          · rcases p116_3 (m.d 0 2) (by simp) with h146 | h146
                                            · rcases p116_3 (m.d 0 3) (by simp) with h147 | h147
                                              · linarith only [h147, h4, hlam]
                                              · rcases p116_3 (m.d 0 4) (by simp) with h149 | h149
                                                · linarith only [h149, h5, hlam]
                                                · rcases p116_3 (m.d 0 5) (by simp) with h151 | h151
                                                  · linarith only [h151, h6, hlam]
                                                  · linarith only [h151, h79, hlam]
                                            · linarith only [h146, h5, hlam]
                                          · linarith only [h145, h2, hlam]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          rcases p116_3 (m.d 0 1) (by simp) with h156 | h156
                                          · rcases p116_3 (m.d 0 2) (by simp) with h157 | h157
                                            · rcases p116_3 (m.d 0 3) (by simp) with h158 | h158
                                              · linarith only [h158, h4, hlam]
                                              · rcases p116_3 (m.d 0 4) (by simp) with h160 | h160
                                                · linarith only [h160, h5, hlam]
                                                · rcases p116_3 (m.d 0 5) (by simp) with h162 | h162
                                                  · linarith only [h162, h6, hlam]
                                                  · rcases h5bigk with h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [hlam, p164_0]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p116_1, p164_1, u2elo0]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h108, h112, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p116_1, p164_1, u2elo0]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h59, hlam, p164_1]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h79, hlam, p164_1]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h3, hlam, p164_0]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [hlam, p164_0]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h108, h112, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p164_1, u0elo0]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h104, hlam, p164_1]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h106, hlam, p164_1]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h6, hlam, p164_1]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h101, hlam, p164_1]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [hlam, p164_0]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h110, hlam, p164_1]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h112, hlam, p164_1]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h108, h112, h6, hc23, hlam, hphi, p164_1, u3elo4]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h101, h108, h112, hc23, hlam, hphi, p164_1, u3elo4]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h108, h112, hc23, hlam, hphi, p164_1, u3elo4]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [hlam, p164_0]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h114, hlam, p164_1]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      rcases p164_3 (m.d 0 5) (by simp) with h185 | h185
                                                      · linarith only [h185, h79, hlam]
                                                      · rcases p164_3 (m.d 1 5) (by simp) with h187 | h187
                                                        · linarith only [h106, h187, hlam]
                                                        · rcases p164_3 (m.d 2 5) (by simp) with h189 | h189
                                                          · linarith only [h112, h189, hlam]
                                                          · rcases p164_3 (m.d 3 5) (by simp) with h191 | h191
                                                            · linarith only [h114, h191, hlam]
                                                            · linarith only [h191, h59, hlam]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      rcases p164_3 (m.d 0 5) (by simp) with h194 | h194
                                                      · linarith only [h194, h79, hlam]
                                                      · linarith only [h194, h3, hlam]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      rcases p164_3 (m.d 0 5) (by simp) with h197 | h197
                                                      · linarith only [h197, h79, hlam]
                                                      · linarith only [h197, h6, hlam]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [h1, h59, h99, hc23, hc45, hlam, hphi, ht34, p164_1]
                                                    · have p164_0 := h164c.1
                                                      have p164_1 := h164c.2.1
                                                      have p164_2 := h164c.2.2.1
                                                      have p164_3 := h164c.2.2.2
                                                      linarith only [hlam, p164_0]
                                            · linarith only [h157, h6, hlam]
                                          · linarith only [h156, h3, hlam]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h1, hlam, p116_1]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h4, hlam, p116_1]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [hlam, p116_0]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h7, hlam, p116_1]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h59, hlam, p116_1]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h2, hlam, p116_0]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h5, hlam, p116_0]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h1, h114, h7, h99, hc23, hc45, hlam, hphi, ht34, p116_1]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [hlam, p116_0]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h79, hlam, p116_0]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h3, hlam, p116_0]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h6, hlam, p116_1]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h1, h59, h99, hc23, hlam, hphi, p116_1, u3elo4]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [h108, h5, h59, hc23, hlam, hphi, p116_1, u3elo4]
                                        · have p116_0 := h116c.1
                                          have p116_1 := h116c.2.1
                                          have p116_2 := h116c.2.2.1
                                          have p116_3 := h116c.2.2.2
                                          linarith only [hlam, p116_0]
                        · linarith only [h101, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h100, h5, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h4, h99, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h222 | h222
              · rcases m.htr 0 3 5 (by decide) (by decide) with h223 | h223
                · linarith only [h223, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h225 | h225
                  · linarith only [h225, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h227 | h227
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h228 | h228
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h229 | h229
                        · linarith only [h0, h229, h6, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h231 | h231
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h232 | h232
                            · linarith only [h1, h223, h232, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
                              · linarith only [h2, h225, h234, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                                · linarith only [h0, h227, h236, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                                · linarith only [h1, h223, h231, h236, hc23, hlam, hphi, u3elo4]
                          · linarith only [h222, h223, h231, hc13, hlam, hphi, u3elo4]
                      · linarith only [h228, h5, h6, hc12, hlam, hphi, u2elo4]
                    · linarith only [h227, h4, h6, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h242 | h242
                · linarith only [h222, h242, h4, h6, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h244 | h244
                  · linarith only [h244, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h246 | h246
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h247 | h247
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h248 | h248
                        · linarith only [h0, h248, h6, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                          · linarith only [h222, h250, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h252 | h252
                            · linarith only [h0, h1, h222, h242, h246, h252, h6, hc23, hlam, hphi, u3elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h254 | h254
                              · linarith only [h2, h244, h254, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                                · linarith only [h0, h222, h246, h256, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h258 | h258
                                  · linarith only [h242, h258, h3, h4, h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                                  · linarith only [h0, h247, h256, h258, h6, hc23, hlam, hphi, u3elo4]
                      · linarith only [h247, h5, h6, hc12, hlam, hphi, u2elo4]
                    · linarith only [h246, h4, h6, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h263 | h263
            · rcases m.htr 0 3 4 (by decide) (by decide) with h264 | h264
              · linarith only [h264, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h266 | h266
                · rcases m.htr 0 4 5 (by decide) (by decide) with h267 | h267
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
                      · linarith only [h0, h269, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                          · linarith only [h264, h272, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h274 | h274
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h275 | h275
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                                · linarith only [h0, h1, h264, h268, h274, h276, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                                · linarith only [h0, h268, h276, h5, hc23, hlam, hphi, u3elo3]
                              · linarith only [h267, h268, h269, h275, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h264, h266, h274, hc13, hlam, hphi, u3elo3]
                        · linarith only [h263, h268, h271, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h268, h4, h5, hc12, hlam, hphi, u2elo3]
                  · linarith only [h264, h266, h267, h4, h5, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h286 | h286
                      · linarith only [h0, h286, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h289 | h289
                          · linarith only [h1, h264, h289, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h291 | h291
                            · linarith only [h1, h266, h291, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                                · linarith only [h0, h264, h285, h294, h5, hlam]
                                · linarith only [h0, h285, h294, h5, hc23, hlam, hphi, u3elo3]
                              · linarith only [h264, h284, h285, h286, h293, hc23, hlam, hphi, u3elo3]
                        · linarith only [h263, h285, h288, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h285, h4, h5, hc12, hlam, hphi, u2elo3]
                  · linarith only [h263, h284, h5, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h301 | h301
              · linarith only [h301, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h303 | h303
                · linarith only [h263, h303, h4, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h305 | h305
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h307 | h307
                      · linarith only [h0, h307, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h309 | h309
                        · linarith only [h0, h263, h309, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h311 | h311
                          · linarith only [h1, h301, h311, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h313 | h313
                            · linarith only [h1, h303, h313, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h316 | h316
                                · linarith only [h0, h301, h306, h316, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                                · linarith only [h316, h4, h5, hc23, hlam, hphi, u3elo3]
                              · linarith only [h301, h305, h306, h307, h315, hc23, hlam, hphi, u3elo3]
                    · linarith only [h306, h4, h5, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h321 | h321
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h322 | h322
                      · linarith only [h0, h322, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
                        · linarith only [h0, h263, h324, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h326 | h326
                          · linarith only [h1, h301, h326, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h328 | h328
                            · linarith only [h1, h2, h301, h303, h305, h321, h322, h328, hc23, hlam, hphi, u3elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h330 | h330
                              · linarith only [h2, h305, h330, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h332 | h332
                                · linarith only [h0, h301, h321, h332, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                                · linarith only [h332, h4, h5, hc23, hlam, hphi, u3elo3]
                    · linarith only [h321, h4, h5, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h336 | h336
          · rcases m.htr 0 2 5 (by decide) (by decide) with h337 | h337
            · rcases m.htr 0 3 4 (by decide) (by decide) with h338 | h338
              · rcases m.htr 0 3 5 (by decide) (by decide) with h339 | h339
                · rcases m.htr 0 4 5 (by decide) (by decide) with h340 | h340
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                    · linarith only [h341, h4, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h343 | h343
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h348 | h348
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h349 | h349
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h350 | h350
                                    · linarith only [h0, h343, h350, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                    · linarith only [h336, h340, h350, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · linarith only [h349, h4, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h2, h336, h347, h348, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h336, h340, h347, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h339, h346, hc13, hlam, hphi, u3elo0]
                          · linarith only [h338, h341, h343, h345, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h337, h343, h344, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h336, h343, h4, hc12, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
                    · linarith only [h360, h4, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h362 | h362
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h363 | h363
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h364 | h364
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h365 | h365
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h366 | h366
                              · linarith only [h2, h340, h366, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h368 | h368
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h369 | h369
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h370 | h370
                                    · linarith only [h0, h340, h362, h370, h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h372 | h372
                                      · linarith only [h2, h340, h362, h368, h372, hlam]
                                      · rcases h0bigk with h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h0, h363, h370, hc24, hlam, hphi, ht0b, ht45, ht5b, p374_1, u0elo0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h1, h360, h363, h368, h370, hc34, hlam, hphi, ht0b, ht45, ht5b, p374_1, u0elo0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          rcases p374_3 (m.d 0 1) (by simp) with h378 | h378
                                          · rcases p374_3 (m.d 0 2) (by simp) with h379 | h379
                                            · linarith only [h0, h379, hlam]
                                            · linarith only [h336, h379, hlam]
                                          · linarith only [h2, h378, hlam]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          rcases p374_3 (m.d 0 1) (by simp) with h383 | h383
                                          · rcases p374_3 (m.d 0 2) (by simp) with h384 | h384
                                            · linarith only [h0, h384, hlam]
                                            · linarith only [h337, h384, hlam]
                                          · linarith only [h3, h383, hlam]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h0, hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h4, hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h2, h362, h368, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p374_1, u3elo2]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p374_1, u3elo2]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h1, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hc02, hlam, hphi, ht23, p374_1, u3elo0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          rcases p374_3 (m.d 0 1) (by simp) with h396 | h396
                                          · rcases p374_3 (m.d 0 2) (by simp) with h397 | h397
                                            · linarith only [h397, h4, hlam]
                                            · linarith only [h336, h397, hlam]
                                          · linarith only [h2, h396, hlam]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          rcases p374_3 (m.d 0 1) (by simp) with h401 | h401
                                          · rcases p374_3 (m.d 0 2) (by simp) with h402 | h402
                                            · linarith only [h4, h402, hlam]
                                            · linarith only [h337, h402, hlam]
                                          · linarith only [h3, h401, hlam]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h2, hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h336, hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h338, hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h340, hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h3, hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h337, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h339, hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h2, h337, h362, h368, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p374_1, u3elo2]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hlam, p374_0]
                                  · linarith only [h369, h4, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h0, h363, h368, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · linarith only [h339, h360, h362, h365, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h338, h360, h362, h364, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h337, h362, h363, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h336, h362, h4, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h337, h339, h4, hlam]
              · linarith only [h336, h338, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h424 | h424
              · rcases m.htr 0 3 5 (by decide) (by decide) with h425 | h425
                · rcases m.htr 0 4 5 (by decide) (by decide) with h426 | h426
                  · linarith only [h336, h337, h426, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                    · linarith only [h0, h4, h428, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
                        · linarith only [h337, h431, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h434 | h434
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h435 | h435
                              · linarith only [h0, h4, h426, h430, h435, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h437 | h437
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h438 | h438
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h439 | h439
                                    · linarith only [h336, h337, h426, h439, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h441 | h441
                                      · linarith only [h0, h337, h430, h437, h439, h441, hlam]
                                      · rcases h0bigk with h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h0, h430, h437, hc34, hlam, hphi, ht0b, ht45, ht5b, p443_1, u0elo0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h0, h337, h425, h430, h437, hc34, hlam, hphi, ht0b, ht45, ht5b, p443_1, u0elo0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          rcases p443_3 (m.d 0 1) (by simp) with h447 | h447
                                          · rcases p443_3 (m.d 0 2) (by simp) with h448 | h448
                                            · linarith only [h0, h448, hlam]
                                            · linarith only [h336, h448, hlam]
                                          · linarith only [h2, h447, hlam]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h0, h337, h430, h437, hc34, hlam, hphi, ht0b, ht45, ht5b, p443_1, u0elo0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h0, hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h4, hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h337, h438, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p443_1, u3elo2]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h337, hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h1, hlam, p443_1]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h0, h430, hc24, hlam, hphi, ht0b, ht45, ht5b, p443_1, u0elo2]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          rcases p443_3 (m.d 0 1) (by simp) with h461 | h461
                                          · rcases p443_3 (m.d 0 2) (by simp) with h462 | h462
                                            · linarith only [h4, h462, hlam]
                                            · linarith only [h336, h462, hlam]
                                          · linarith only [h2, h461, hlam]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h0, h337, h430, h437, hc34, hlam, hphi, ht0b, ht45, ht5b, p443_1, u0elo2]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h2, hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h336, hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h424, hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h426, hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h3, hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h0, h430, h437, hc34, hlam, hphi, ht0b, ht45, ht5b, p443_1, u0elo4]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [h425, hlam, p443_0]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          rcases p443_3 (m.d 0 1) (by simp) with h475 | h475
                                          · rcases p443_3 (m.d 0 2) (by simp) with h476 | h476
                                            · linarith only [h337, h476, hlam]
                                            · linarith only [h336, h476, hlam]
                                          · linarith only [h2, h475, hlam]
                                        · have p443_0 := h443c.1
                                          have p443_1 := h443c.2.1
                                          have p443_2 := h443c.2.2.1
                                          have p443_3 := h443c.2.2.2
                                          linarith only [hlam, p443_0]
                                  · linarith only [h0, h4, h430, h437, h438, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h0, h4, h430, h437, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h425, h434, hc13, hlam, hphi, u3elo0]
                          · linarith only [h4, h424, h428, h430, h433, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h336, h337, h430, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h486 | h486
                  · linarith only [h336, h4, h425, h486, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                    · linarith only [h0, h4, h425, h488, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h491 | h491
                        · linarith only [h337, h491, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h494 | h494
                            · linarith only [h1, h425, h494, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h496 | h496
                              · linarith only [h0, h4, h486, h490, h496, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h498 | h498
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h499 | h499
                                  · linarith only [h4, h425, h499, hc02, hlam, hphi, u2elo2]
                                  · linarith only [h0, h4, h490, h498, h499, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h4, h498, hc02, hlam, hphi, ht23, u3elo3]
                          · linarith only [h336, h4, h424, h493, hc13, hlam, hphi, u3elo2]
                      · linarith only [h336, h4, h425, h490, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h336, h4, h424, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h506 | h506
            · rcases m.htr 0 3 4 (by decide) (by decide) with h507 | h507
              · rcases m.htr 0 3 5 (by decide) (by decide) with h508 | h508
                · rcases m.htr 0 4 5 (by decide) (by decide) with h509 | h509
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h510 | h510
                    · linarith only [h0, h4, h510, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h512 | h512
                      · linarith only [h336, h512, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h514 | h514
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h515 | h515
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h516 | h516
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h517 | h517
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h518 | h518
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h519 | h519
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h520 | h520
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h521 | h521
                                      · linarith only [h1, h515, h521, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                      · linarith only [h2, h517, h521, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · linarith only [h1, h336, h515, h517, h520, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                  · linarith only [h0, h336, h514, h518, h519, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                                · linarith only [h0, h4, h514, h518, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h4, h506, h509, h512, h514, h517, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · linarith only [h4, h508, h516, hc13, hlam, hphi, u3elo2]
                          · linarith only [h4, h507, h510, h514, h515, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · linarith only [h4, h506, h514, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h336, h506, h509, hlam]
                · linarith only [h336, h506, h507, h508, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h533 | h533
                · rcases m.htr 0 4 5 (by decide) (by decide) with h534 | h534
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                    · linarith only [h0, h4, h535, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h537 | h537
                      · linarith only [h0, h336, h537, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h539 | h539
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h540 | h540
                          · linarith only [h4, h507, h540, hc02, hlam, hphi, ht23, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h542 | h542
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h543 | h543
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h544 | h544
                                · linarith only [h0, h4, h507, h539, h544, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                · linarith only [h0, h4, h539, h544, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h507, h534, h540, h543, hc13, hlam, hphi, u3elo3]
                            · linarith only [h533, h535, h539, h542, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h506, h539, hc12, hlam, hphi, u2elo0]
                  · linarith only [h336, h506, h534, hlam]
                · linarith only [h4, h506, h533, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h552 | h552
              · rcases m.htr 0 3 5 (by decide) (by decide) with h553 | h553
                · rcases m.htr 0 4 5 (by decide) (by decide) with h554 | h554
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h555 | h555
                    · linarith only [h0, h4, h555, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h557 | h557
                      · linarith only [h336, h557, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h559 | h559
                        · linarith only [h0, h506, h559, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h561 | h561
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h562 | h562
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h563 | h563
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h564 | h564
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h565 | h565
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h566 | h566
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h567 | h567
                                      · linarith only [h1, h561, h567, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                      · linarith only [h2, h563, h567, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · linarith only [h2, h336, h563, h566, hlam]
                                  · linarith only [h2, h3, h336, h562, h563, h564, h565, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h4, h564, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h4, h552, h554, h557, h563, hc12, hlam, hphi, ht23, u3elo2]
                            · linarith only [h4, h553, h561, h562, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h4, h552, h561, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h576 | h576
                    · linarith only [h0, h4, h552, h576, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h578 | h578
                      · linarith only [h0, h336, h578, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h580 | h580
                        · linarith only [h0, h506, h580, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h582 | h582
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h583 | h583
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h584 | h584
                              · linarith only [h336, h554, h582, h584, hc02, hlam, hphi, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h586 | h586
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h587 | h587
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h588 | h588
                                    · linarith only [h0, h336, h554, h588, hc12, hlam, hphi, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h590 | h590
                                      · linarith only [h0, h336, h588, h590, hc12, hlam, hphi, ht23, u3elo3]
                                      · rcases h0bigk with h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          rcases p592_3 (m.d 0 1) (by simp) with h594 | h594
                                          · rcases p592_3 (m.d 0 2) (by simp) with h595 | h595
                                            · linarith only [h0, h595, hlam]
                                            · rcases p592_3 (m.d 0 3) (by simp) with h597 | h597
                                              · linarith only [h1, h597, hlam]
                                              · linarith only [h4, h597, hlam]
                                          · linarith only [h0, h594, hlam]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h1, h583, hc35, hlam, hphi, ht0b, ht5b, p592_1, u0elo0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          rcases p592_3 (m.d 0 1) (by simp) with h602 | h602
                                          · rcases p592_3 (m.d 0 2) (by simp) with h603 | h603
                                            · linarith only [h0, h603, hlam]
                                            · rcases p592_3 (m.d 0 3) (by simp) with h605 | h605
                                              · linarith only [h1, h605, hlam]
                                              · linarith only [h552, h605, hlam]
                                          · linarith only [h2, h602, hlam]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          rcases p592_3 (m.d 0 1) (by simp) with h609 | h609
                                          · rcases p592_3 (m.d 0 2) (by simp) with h610 | h610
                                            · linarith only [h0, h610, hlam]
                                            · rcases p592_3 (m.d 0 3) (by simp) with h612 | h612
                                              · linarith only [h1, h612, hlam]
                                              · linarith only [h553, h612, hlam]
                                          · linarith only [h3, h609, hlam]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h0, hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h4, hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h336, hlam, p592_1]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h506, hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h1, hlam, p592_1]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, ht23, p592_1, u3elo0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h0, h336, h4, hc12, hlam, hphi, p592_1, u2elo2]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h0, h4, h506, hc12, hlam, hphi, ht23, p592_1, u3elo2]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h2, hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h0, h336, hc12, hlam, hphi, p592_1, u2elo3]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h552, hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h554, hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h3, hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h0, h506, hc12, hlam, hphi, p592_1, u2elo4]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h553, hlam, p592_0]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [h0, h336, h4, h553, hc12, hlam, hphi, ht23, p592_1, u3elo2]
                                        · have p592_0 := h592c.1
                                          have p592_1 := h592c.2.1
                                          have p592_2 := h592c.2.2.1
                                          have p592_3 := h592c.2.2.2
                                          linarith only [hlam, p592_0]
                                  · linarith only [h0, h4, h587, hc12, hlam, hphi, ht23, u3elo4]
                                · linarith only [h0, h1, h4, h582, h586, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h4, h553, h583, hc13, hlam, hphi, u3elo2]
                          · linarith only [h4, h552, h576, h582, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h640 | h640
                  · linarith only [h552, h553, h640, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h642 | h642
                    · linarith only [h0, h4, h642, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h644 | h644
                      · linarith only [h0, h336, h644, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h646 | h646
                        · linarith only [h0, h506, h646, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h648 | h648
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h649 | h649
                            · linarith only [h1, h553, h649, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h651 | h651
                              · linarith only [h0, h1, h2, h336, h553, h640, h648, h651, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, u0elo0, u3elo4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h653 | h653
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h654 | h654
                                  · linarith only [h1, h553, h648, h654, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · linarith only [h0, h4, h654, hc12, hlam, hphi, ht23, u3elo4]
                                · linarith only [h0, h1, h4, h648, h653, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h552, h553, h648, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h659 | h659
                · rcases m.htr 0 4 5 (by decide) (by decide) with h660 | h660
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h661 | h661
                    · linarith only [h0, h4, h661, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h663 | h663
                      · linarith only [h0, h336, h663, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h665 | h665
                        · linarith only [h0, h506, h665, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
                          · linarith only [h506, h552, h659, h667, hc02, hlam, hphi, ht23, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h669 | h669
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h670 | h670
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h671 | h671
                                · linarith only [h1, h552, h669, h671, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                · linarith only [h0, h4, h671, hc12, hlam, hphi, ht23, u3elo3]
                              · linarith only [h336, h660, h663, h670, hc12, hlam, hphi, u2elo3]
                            · linarith only [h552, h659, h669, hc13, hlam, hphi, u3elo3]
                  · linarith only [h552, h659, h660, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h677 | h677
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h678 | h678
                    · linarith only [h0, h4, h678, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h680 | h680
                      · linarith only [h0, h336, h680, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h682 | h682
                        · linarith only [h0, h506, h682, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h684 | h684
                          · linarith only [h1, h552, h684, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h686 | h686
                            · linarith only [h1, h659, h686, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h688 | h688
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h689 | h689
                                · linarith only [h1, h552, h678, h689, hc12, hlam, hphi, u2elo2]
                                · linarith only [h4, h689, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h552, h677, h680, h688, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h693 | h693
                    · linarith only [h0, h4, h693, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h695 | h695
                      · linarith only [h0, h336, h695, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h697 | h697
                        · linarith only [h0, h506, h697, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h699 | h699
                          · linarith only [h4, h552, h699, hc02, hlam, hphi, ht23, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h701 | h701
                            · linarith only [h1, h659, h701, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h703 | h703
                              · linarith only [h2, h677, h703, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
                                · linarith only [h552, h705, hc03, hlam, hphi, u3elo2]
                                · linarith only [h0, h4, h705, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h708 | h708
        · rcases m.htr 0 2 4 (by decide) (by decide) with h709 | h709
          · rcases m.htr 0 2 5 (by decide) (by decide) with h710 | h710
            · linarith only [h0, h3, h710, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h712 | h712
              · rcases m.htr 0 3 5 (by decide) (by decide) with h713 | h713
                · linarith only [h1, h3, h713, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h715 | h715
                  · linarith only [h2, h3, h715, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h717 | h717
                    · linarith only [h0, h3, h713, h717, hc23, hlam, hphi, u3elo4]
                    · linarith only [h708, h710, h717, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h720 | h720
                · linarith only [h1, h3, h712, h720, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h722 | h722
                  · linarith only [h0, h3, h709, h710, h722, hc12, hlam, hphi, u2elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h724 | h724
                    · linarith only [h0, h3, h720, h724, hc23, hlam, hphi, u3elo4]
                    · linarith only [h708, h710, h724, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h727 | h727
            · linarith only [h2, h3, h709, h727, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h729 | h729
              · linarith only [h708, h709, h729, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h731 | h731
                · linarith only [h2, h3, h708, h709, h731, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h733 | h733
                  · linarith only [h2, h3, h733, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h735 | h735
                    · linarith only [h0, h3, h731, h735, hc23, hlam, hphi, u3elo4]
                    · linarith only [h708, h709, h735, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h738 | h738
          · rcases m.htr 0 2 5 (by decide) (by decide) with h739 | h739
            · linarith only [h0, h3, h708, h739, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h741 | h741
              · rcases m.htr 0 3 5 (by decide) (by decide) with h742 | h742
                · linarith only [h1, h3, h742, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h744 | h744
                  · linarith only [h0, h3, h708, h738, h742, h744, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h746 | h746
                    · linarith only [h0, h708, h742, h746, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h748 | h748
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h749 | h749
                        · linarith only [h0, h3, h708, h739, h749, hc01, hlam, hphi, ht12, u2elo2]
                        · linarith only [h1, h3, h746, h748, h749, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h708, h738, h748, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h708, h738, h741, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h754 | h754
            · linarith only [h0, h3, h738, h754, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h756 | h756
              · rcases m.htr 0 3 5 (by decide) (by decide) with h757 | h757
                · linarith only [h1, h3, h757, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
                  · linarith only [h0, h3, h756, h757, h759, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h761 | h761
                    · linarith only [h0, h738, h756, h757, h761, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h763 | h763
                      · linarith only [h0, h738, h763, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h765 | h765
                        · linarith only [h1, h3, h754, h761, h765, hlam]
                        · linarith only [h1, h3, h761, h765, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h768 | h768
                · linarith only [h1, h3, h756, h768, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h770 | h770
                  · linarith only [h2, h3, h770, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
                    · linarith only [h0, h708, h772, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h774 | h774
                      · linarith only [h0, h738, h774, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h776 | h776
                        · linarith only [h0, h754, h776, hlam]
                        · linarith only [h1, h3, h772, h776, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h779 | h779
      · rcases m.htr 0 2 3 (by decide) (by decide) with h780 | h780
        · rcases m.htr 0 2 4 (by decide) (by decide) with h781 | h781
          · linarith only [h0, h2, h781, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h783 | h783
            · rcases m.htr 0 3 4 (by decide) (by decide) with h784 | h784
              · linarith only [h1, h2, h784, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h786 | h786
                · rcases m.htr 0 4 5 (by decide) (by decide) with h787 | h787
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
                    · linarith only [h0, h2, h784, h788, hc23, hlam, hphi, u3elo3]
                    · linarith only [h780, h781, h788, hc12, hlam, hphi, u2elo3]
                  · linarith only [h0, h2, h784, h786, h787, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h792 | h792
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h793 | h793
                    · linarith only [h0, h2, h784, h793, hc23, hlam, hphi, u3elo3]
                    · linarith only [h780, h781, h793, hc12, hlam, hphi, u2elo3]
                  · linarith only [h0, h2, h781, h783, h792, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h797 | h797
              · linarith only [h1, h2, h797, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h799 | h799
                · linarith only [h780, h783, h799, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h801 | h801
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                    · linarith only [h0, h2, h797, h802, hc23, hlam, hphi, u3elo3]
                    · linarith only [h780, h783, h802, hc12, hlam, hphi, u2elo4]
                  · linarith only [h2, h779, h801, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h806 | h806
          · linarith only [h1, h2, h780, h806, hc13, hlam, hphi, u3elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h808 | h808
            · rcases m.htr 0 3 4 (by decide) (by decide) with h809 | h809
              · linarith only [h1, h2, h809, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h811 | h811
                · rcases m.htr 0 4 5 (by decide) (by decide) with h812 | h812
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h813 | h813
                    · linarith only [h0, h780, h809, h813, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h815 | h815
                      · linarith only [h806, h815, hc02, hlam, hphi, u2elo1]
                      · linarith only [h1, h2, h813, h815, hc12, hlam, hphi, u2elo3]
                  · linarith only [h0, h2, h780, h808, h812, hc12, hlam, hphi, u2elo2]
                · linarith only [h780, h808, h811, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h820 | h820
              · linarith only [h1, h2, h820, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h822 | h822
                · rcases m.htr 0 4 5 (by decide) (by decide) with h823 | h823
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h824 | h824
                    · linarith only [h0, h808, h820, h822, h824, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h826 | h826
                      · linarith only [h0, h806, h826, hlam]
                      · linarith only [h0, h2, h826, hc12, hlam, hphi, u2elo3]
                  · linarith only [h0, h2, h820, h822, h823, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h830 | h830
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h831 | h831
                    · linarith only [h0, h780, h820, h831, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h833 | h833
                      · linarith only [h0, h2, h806, h833, hlam]
                      · linarith only [h1, h2, h831, h833, hc12, hlam, hphi, u2elo3]
                  · linarith only [h2, h779, h830, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h837 | h837
        · rcases m.htr 0 2 4 (by decide) (by decide) with h838 | h838
          · linarith only [h0, h2, h838, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h840 | h840
            · linarith only [h0, h779, h838, h840, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h842 | h842
              · linarith only [h1, h2, h842, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h844 | h844
                · linarith only [h0, h779, h837, h838, h844, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h846 | h846
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h847 | h847
                    · linarith only [h0, h779, h842, h846, h847, hc23, hlam, hphi, u3elo3]
                    · linarith only [h837, h838, h847, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h850 | h850
                    · linarith only [h0, h2, h844, h846, h850, hc23, hlam, hphi, u3elo4]
                    · linarith only [h837, h838, h850, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h853 | h853
          · linarith only [h0, h2, h853, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h855 | h855
            · linarith only [h1, h779, h837, h855, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h857 | h857
              · linarith only [h1, h2, h857, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h859 | h859
                · linarith only [h0, h779, h857, h859, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h861 | h861
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h862 | h862
                    · linarith only [h0, h837, h857, h862, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h864 | h864
                      · linarith only [h1, h779, h853, h861, h862, h864, hlam]
                      · linarith only [h1, h2, h862, h864, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h867 | h867
                    · linarith only [h0, h837, h867, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h869 | h869
                      · linarith only [h1, h2, h861, h867, h869, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h2, h867, h869, hc12, hlam, hphi, u2elo3]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
