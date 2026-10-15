import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
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
                              · linarith only [h0, h10, h16, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h10, h13, h16, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                              · linarith only [h0, h10, h19, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h10, h13, h19, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h0, h13, h14, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                          · linarith only [h0, h13, h23, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                              · linarith only [h0, h13, h26, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                                · linarith only [h10, h23, h28, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                                  · linarith only [h0, h11, h30, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h2, h25, h26, h30, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                              · linarith only [h0, h10, h33, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                                · linarith only [h0, h10, h13, h25, h35, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                                  · linarith only [h0, h13, h25, h37, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                                    · linarith only [h10, h13, h25, h39, hc34, hlam, hphi, u3ehi2]
                                    · linarith only [h10, h13, h39, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h10, h11, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                      · linarith only [h0, h10, h4, h45, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                            · linarith only [h0, h10, h4, h44, h49, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                              · linarith only [h0, h10, h4, h44, h51, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h10, h44, h47, h51, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h4, h47, h48, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h10, h44, h47, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                      · linarith only [h0, h10, h4, h56, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                                    · linarith only [h1, h58, h64, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h2, h60, h64, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h44, h60, h63, hlam]
                                · linarith only [h10, h59, h62, hlam]
                              · linarith only [h10, h59, h61, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                                  · linarith only [h0, h5, h58, h60, h72, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h74 | h74
                                    · linarith only [h44, h58, h72, h74, hlam]
                                    · rcases h1bigk with h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h0, h4, h44, h7, h72, h9, hlam, p76_2]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h59, h74, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        rcases p76_3 (m.d 0 1) (by simp) with h80 | h80
                                        · rcases p76_3 (m.d 1 2) (by simp) with h81 | h81
                                          · linarith only [h0, h81, hlam]
                                          · rcases p76_3 (m.d 1 3) (by simp) with h83 | h83
                                            · linarith only [h1, h83, hlam]
                                            · linarith only [h58, h83, hlam]
                                        · linarith only [h80, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        rcases p76_3 (m.d 0 1) (by simp) with h87 | h87
                                        · rcases p76_3 (m.d 1 2) (by simp) with h88 | h88
                                          · linarith only [h0, h88, hlam]
                                          · rcases p76_3 (m.d 1 3) (by simp) with h90 | h90
                                            · linarith only [h1, h90, hlam]
                                            · linarith only [h59, h90, hlam]
                                        · linarith only [h87, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h0, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h10, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h44, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h56, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h1, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        rcases p76_3 (m.d 0 1) (by simp) with h100 | h100
                                        · rcases p76_3 (m.d 1 2) (by simp) with h101 | h101
                                          · linarith only [h10, h101, hlam]
                                          · rcases p76_3 (m.d 1 3) (by simp) with h103 | h103
                                            · rcases p76_3 (m.d 1 4) (by simp) with h104 | h104
                                              · linarith only [h104, h58, hlam]
                                              · linarith only [h104, h44, hlam]
                                            · linarith only [h10, h103, hlam]
                                        · linarith only [h0, h100, hlam]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h1, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h0, h10, h4, hc01, hlam, hphi, ht0b, ht5b, p76_1, u5ehi1]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h2, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h44, h7, h72, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h58, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h60, hlam, p76_1]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h3, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        rcases p76_3 (m.d 0 1) (by simp) with h118 | h118
                                        · rcases p76_3 (m.d 1 2) (by simp) with h119 | h119
                                          · linarith only [h119, h56, hlam]
                                          · rcases p76_3 (m.d 1 3) (by simp) with h121 | h121
                                            · rcases p76_3 (m.d 1 4) (by simp) with h122 | h122
                                              · linarith only [h122, h60, hlam]
                                              · linarith only [h122, h44, hlam]
                                            · linarith only [h10, h121, hlam]
                                        · linarith only [h0, h118, hlam]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h59, hlam, p76_0]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [h3, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                      · have p76_0 := h76c.1
                                        have p76_1 := h76c.2.1
                                        have p76_2 := h76c.2.2.1
                                        have p76_3 := h76c.2.2.2
                                        linarith only [hlam, p76_0]
                                · linarith only [h0, h10, h4, h58, h71, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h10, h58, h70, hlam]
                          · linarith only [h58, h59, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                          · linarith only [h0, h133, h4, h58, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                              · linarith only [h0, h136, h4, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                                · linarith only [h133, h136, h138, hc34, hlam, hphi, u3ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                                    · rcases h1bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h0, h10, h138, h141, h4, h7, hlam, p142_2]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        rcases p142_3 (m.d 0 1) (by simp) with h145 | h145
                                        · rcases p142_3 (m.d 1 2) (by simp) with h146 | h146
                                          · linarith only [h0, h146, hlam]
                                          · rcases p142_3 (m.d 1 3) (by simp) with h148 | h148
                                            · linarith only [h148, hlam, p142_0]
                                            · rcases p142_3 (m.d 1 4) (by simp) with h150 | h150
                                              · linarith only [h150, h2, hlam]
                                              · linarith only [h150, h58, hlam]
                                        · linarith only [h145, hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h135, hc01, hlam, hphi, ht0b, ht5b, p142_1, u5ehi4]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        rcases p142_3 (m.d 0 1) (by simp) with h155 | h155
                                        · rcases p142_3 (m.d 1 2) (by simp) with h156 | h156
                                          · linarith only [h0, h156, hlam]
                                          · rcases p142_3 (m.d 1 3) (by simp) with h158 | h158
                                            · linarith only [h1, h158, hlam]
                                            · rcases p142_3 (m.d 1 4) (by simp) with h160 | h160
                                              · linarith only [h160, h2, hlam]
                                              · linarith only [h135, h160, hlam]
                                        · linarith only [h155, hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h0, hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h10, hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h44, hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h56, hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h1, hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h0, h10, h138, h141, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h58, hlam, p142_1]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h133, hlam, p142_1]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h2, hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        rcases p142_3 (m.d 0 1) (by simp) with h175 | h175
                                        · rcases p142_3 (m.d 1 2) (by simp) with h176 | h176
                                          · linarith only [h176, h44, hlam]
                                          · rcases p142_3 (m.d 1 3) (by simp) with h178 | h178
                                            · linarith only [h178, h58, hlam]
                                            · linarith only [h10, h178, hlam]
                                        · linarith only [h0, h175, hlam]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u3ehi1]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h0, h136, h4, h44, h7, hc01, hlam, hphi, ht0b, ht5b, p142_1, u5ehi1]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h3, hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        rcases p142_3 (m.d 0 1) (by simp) with h186 | h186
                                        · rcases p142_3 (m.d 1 2) (by simp) with h187 | h187
                                          · linarith only [h187, h56, hlam]
                                          · rcases p142_3 (m.d 1 3) (by simp) with h189 | h189
                                            · linarith only [h133, h189, hlam]
                                            · linarith only [h10, h189, hlam]
                                        · linarith only [h0, h186, hlam]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u3ehi1]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [h135, hlam, p142_0]
                                      · have p142_0 := h142c.1
                                        have p142_1 := h142c.2.1
                                        have p142_2 := h142c.2.2.1
                                        have p142_3 := h142c.2.2.2
                                        linarith only [hlam, p142_0]
                                    · linarith only [h0, h141, h4, h58, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h135, h140, h44, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                              · linarith only [h0, h198, h4, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h200 | h200
                                · linarith only [h198, h200, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                                  · linarith only [h0, h135, h202, h5, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h204 | h204
                                    · linarith only [h0, h198, h202, h204, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                    · linarith only [h0, h204, h4, h58, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h207 | h207
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h210 | h210
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h211 | h211
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h212 | h212
                            · linarith only [h2, h212, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                              · linarith only [h0, h207, h214, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h2, h210, h214, h9, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h210, h211, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h210, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h0, h207, h209, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h207, h208, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
                      · linarith only [h0, h207, h222, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h226 | h226
                            · linarith only [h0, h207, h221, h226, h4, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                              · linarith only [h0, h207, h221, h228, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h207, h221, h224, h228, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h224, h225, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h224, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h233 | h233
                      · linarith only [h221, h233, h5, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h236 | h236
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                            · linarith only [h2, h221, h237, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h240 | h240
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h241 | h241
                                  · linarith only [h241, h5, h9, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h243 | h243
                                    · linarith only [h0, h207, h235, h243, h4, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases h1bigk with h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        rcases p245_3 (m.d 0 1) (by simp) with h247 | h247
                                        · rcases p245_3 (m.d 1 2) (by simp) with h248 | h248
                                          · linarith only [h248, hlam, p245_0]
                                          · rcases p245_3 (m.d 1 3) (by simp) with h250 | h250
                                            · linarith only [h1, h250, hlam]
                                            · linarith only [h207, h250, hlam]
                                        · linarith only [h247, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h235, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1, u3ehi3]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        rcases p245_3 (m.d 0 1) (by simp) with h255 | h255
                                        · rcases p245_3 (m.d 1 2) (by simp) with h256 | h256
                                          · linarith only [h0, h256, hlam]
                                          · rcases p245_3 (m.d 1 3) (by simp) with h258 | h258
                                            · linarith only [h1, h258, hlam]
                                            · linarith only [h235, h258, hlam]
                                        · linarith only [h255, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        rcases p245_3 (m.d 0 1) (by simp) with h262 | h262
                                        · rcases p245_3 (m.d 1 2) (by simp) with h263 | h263
                                          · linarith only [h0, h263, hlam]
                                          · rcases p245_3 (m.d 1 3) (by simp) with h265 | h265
                                            · linarith only [h1, h265, hlam]
                                            · linarith only [h236, h265, hlam]
                                        · linarith only [h262, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h0, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h207, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h221, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h233, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h1, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        rcases p245_3 (m.d 0 1) (by simp) with h275 | h275
                                        · rcases p245_3 (m.d 1 2) (by simp) with h276 | h276
                                          · linarith only [h207, h276, hlam]
                                          · rcases p245_3 (m.d 1 3) (by simp) with h278 | h278
                                            · rcases p245_3 (m.d 1 4) (by simp) with h279 | h279
                                              · linarith only [h235, h279, hlam]
                                              · linarith only [h221, h279, hlam]
                                            · linarith only [h207, h278, hlam]
                                        · linarith only [h0, h275, hlam]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h0, h207, h235, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1, u3ehi3]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h0, h207, h235, h237, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1, u3ehi3]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h2, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h2, h9, hc12, hc45, hlam, hphi, ht23, ht34, p245_1]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h235, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h237, hlam, p245_1]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h3, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        rcases p245_3 (m.d 0 1) (by simp) with h293 | h293
                                        · rcases p245_3 (m.d 1 2) (by simp) with h294 | h294
                                          · linarith only [h233, h294, hlam]
                                          · rcases p245_3 (m.d 1 3) (by simp) with h296 | h296
                                            · rcases p245_3 (m.d 1 4) (by simp) with h297 | h297
                                              · linarith only [h237, h297, hlam]
                                              · linarith only [h221, h297, hlam]
                                            · linarith only [h207, h296, hlam]
                                        · linarith only [h0, h293, hlam]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h236, hlam, p245_0]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [h0, h207, h235, h236, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1, u3ehi3]
                                      · have p245_0 := h245c.1
                                        have p245_1 := h245c.2.1
                                        have p245_2 := h245c.2.2.1
                                        have p245_3 := h245c.2.2.2
                                        linarith only [hlam, p245_0]
                                · linarith only [h0, h207, h235, h240, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h207, h235, h239, hlam]
                          · linarith only [h235, h236, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h235, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h310 | h310
              · linarith only [h310, h7, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
                · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h314 | h314
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h315 | h315
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h316 | h316
                        · linarith only [h1, h316, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h318 | h318
                          · linarith only [h1, h310, h318, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h320 | h320
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
                              · linarith only [h1, h313, h321, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                                · linarith only [h1, h310, h313, h323, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
                                  · linarith only [h0, h314, h325, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h2, h320, h321, h325, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h312, h313, h316, h320, h7, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h0, h313, h315, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h313, h314, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h332 | h332
                      · linarith only [h313, h332, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h334 | h334
                        · linarith only [h313, h334, h4, h7, hlam]
                        · linarith only [h313, h331, h334, h4, h7, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h337 | h337
                      · linarith only [h0, h331, h337, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h339 | h339
                        · linarith only [h1, h339, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h341 | h341
                          · linarith only [h313, h341, h4, h7, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h343 | h343
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h344 | h344
                              · linarith only [h344, h4, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h346 | h346
                                · linarith only [h310, h346, h4, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h348 | h348
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h349 | h349
                                    · rcases h1bigk with h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        rcases p350_3 (m.d 0 1) (by simp) with h352 | h352
                                        · rcases p350_3 (m.d 1 2) (by simp) with h353 | h353
                                          · linarith only [h353, hlam, p350_0]
                                          · rcases p350_3 (m.d 1 3) (by simp) with h355 | h355
                                            · linarith only [h1, h355, hlam]
                                            · linarith only [h313, h355, hlam]
                                        · linarith only [h352, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        rcases p350_3 (m.d 0 1) (by simp) with h359 | h359
                                        · rcases p350_3 (m.d 1 2) (by simp) with h360 | h360
                                          · linarith only [h0, h360, hlam]
                                          · rcases p350_3 (m.d 1 3) (by simp) with h362 | h362
                                            · linarith only [h362, hlam, p350_0]
                                            · rcases p350_3 (m.d 1 4) (by simp) with h364 | h364
                                              · linarith only [h2, h364, hlam]
                                              · linarith only [h339, h364, hlam]
                                        · linarith only [h359, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h343, hc01, hlam, hphi, ht0b, ht5b, p350_1, u5ehi4]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        rcases p350_3 (m.d 0 1) (by simp) with h369 | h369
                                        · rcases p350_3 (m.d 1 2) (by simp) with h370 | h370
                                          · linarith only [h0, h370, hlam]
                                          · rcases p350_3 (m.d 1 3) (by simp) with h372 | h372
                                            · linarith only [h1, h372, hlam]
                                            · rcases p350_3 (m.d 1 4) (by simp) with h374 | h374
                                              · linarith only [h2, h374, hlam]
                                              · linarith only [h343, h374, hlam]
                                        · linarith only [h369, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h0, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h313, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h331, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h337, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h1, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h1, h310, h349, hc12, hc34, hlam, hphi, ht23, p350_1]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h339, hlam, p350_1]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h341, hlam, p350_1]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h2, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        rcases p350_3 (m.d 0 1) (by simp) with h389 | h389
                                        · rcases p350_3 (m.d 1 2) (by simp) with h390 | h390
                                          · linarith only [h331, h390, hlam]
                                          · rcases p350_3 (m.d 1 3) (by simp) with h392 | h392
                                            · linarith only [h339, h392, hlam]
                                            · linarith only [h313, h392, hlam]
                                        · linarith only [h0, h389, hlam]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h0, h331, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p350_1, u3ehi1]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h0, h331, h341, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p350_1, u3ehi1]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h3, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        rcases p350_3 (m.d 0 1) (by simp) with h400 | h400
                                        · rcases p350_3 (m.d 1 2) (by simp) with h401 | h401
                                          · linarith only [h337, h401, hlam]
                                          · rcases p350_3 (m.d 1 3) (by simp) with h403 | h403
                                            · linarith only [h341, h403, hlam]
                                            · linarith only [h313, h403, hlam]
                                        · linarith only [h0, h400, hlam]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h0, h331, h343, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p350_1, u3ehi1]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [h343, hlam, p350_0]
                                      · have p350_0 := h350c.1
                                        have p350_1 := h350c.2.1
                                        have p350_2 := h350c.2.2.1
                                        have p350_3 := h350c.2.2.2
                                        linarith only [hlam, p350_0]
                                    · linarith only [h349, h4, h7, hc45, hlam, hphi, ht34, u3ehi2]
                                  · linarith only [h331, h343, h348, hlam]
                            · linarith only [h312, h339, h343, h7, hc34, hlam, hphi, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h413 | h413
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h414 | h414
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h415 | h415
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h416 | h416
                        · linarith only [h1, h310, h416, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
                          · linarith only [h1, h312, h418, h7, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h420 | h420
                            · linarith only [h2, h312, h420, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h422 | h422
                              · linarith only [h1, h413, h422, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h424 | h424
                                · linarith only [h1, h310, h413, h424, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h426 | h426
                                  · linarith only [h1, h312, h413, h414, h426, h7, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h428 | h428
                                    · linarith only [h1, h312, h413, h428, h7, hc34, hlam, hphi, u3ehi2]
                                    · linarith only [h1, h413, h428, h7, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h413, h415, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h413, h414, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h433 | h433
                    · linarith only [h312, h4, h413, h433, h7, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h435 | h435
                      · linarith only [h312, h4, h413, h435, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h437 | h437
                        · linarith only [h4, h413, h437, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h439 | h439
                          · linarith only [h310, h4, h413, h439, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h441 | h441
                            · linarith only [h312, h4, h413, h433, h441, h7, hc12, hc24, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h443 | h443
                              · linarith only [h4, h443, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h445 | h445
                                · linarith only [h310, h4, h445, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h447 | h447
                                  · linarith only [h312, h447, h5, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h449 | h449
                                    · linarith only [h312, h4, h413, h449, h7, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h4, h413, h449, h7, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h452 | h452
            · rcases m.htr 0 3 5 (by decide) (by decide) with h453 | h453
              · linarith only [h4, h453, h6, hlam]
              · linarith only [h452, h453, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h456 | h456
              · linarith only [h452, h456, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h458 | h458
                · linarith only [h458, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h461 | h461
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h462 | h462
                      · linarith only [h0, h462, h6, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h464 | h464
                        · linarith only [h1, h452, h458, h464, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h466 | h466
                          · linarith only [h1, h456, h466, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h468 | h468
                            · linarith only [h2, h452, h458, h468, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h470 | h470
                              · linarith only [h1, h452, h460, h470, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h472 | h472
                                · linarith only [h0, h456, h461, h470, h472, h6, hlam]
                                · linarith only [h0, h461, h470, h472, h6, hc35, hlam, hphi, u3ehi2]
                    · linarith only [h461, h5, h6, hc12, hc25, hlam, hphi]
                  · linarith only [h4, h460, h6, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h477 | h477
          · rcases m.htr 0 3 4 (by decide) (by decide) with h478 | h478
            · linarith only [h4, h478, h5, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h480 | h480
              · linarith only [h478, h480, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h482 | h482
                · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h484 | h484
                    · linarith only [h0, h484, h5, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h486 | h486
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h487 | h487
                        · linarith only [h1, h478, h487, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h489 | h489
                          · linarith only [h1, h480, h489, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                              · linarith only [h0, h478, h483, h492, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · linarith only [h4, h492, h5, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h483, h484, h491, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h477, h483, h486, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h4, h483, h5, hc12, hc24, hlam, hphi]
                · linarith only [h4, h482, h5, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h499 | h499
            · linarith only [h4, h499, h5, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h501 | h501
              · linarith only [h499, h501, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h503 | h503
                · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
                    · linarith only [h0, h5, h505, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h507 | h507
                      · linarith only [h0, h477, h507, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h509 | h509
                        · linarith only [h1, h499, h509, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h511 | h511
                          · linarith only [h0, h1, h477, h501, h504, h511, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h513 | h513
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                              · linarith only [h0, h499, h504, h514, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · linarith only [h0, h5, h504, h514, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h499, h503, h504, h505, h513, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h4, h5, h504, hc12, hc24, hlam, hphi]
                · linarith only [h4, h5, h503, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h520 | h520
        · rcases m.htr 0 2 5 (by decide) (by decide) with h521 | h521
          · rcases m.htr 0 3 4 (by decide) (by decide) with h522 | h522
            · rcases m.htr 0 3 5 (by decide) (by decide) with h523 | h523
              · rcases m.htr 0 4 5 (by decide) (by decide) with h524 | h524
                · rcases m.htr 1 2 3 (by decide) (by decide) with h525 | h525
                  · linarith only [h4, h521, h525, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h527 | h527
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h528 | h528
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h529 | h529
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h530 | h530
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h531 | h531
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h532 | h532
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h533 | h533
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h534 | h534
                                  · linarith only [h0, h4, h527, h534, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                  · linarith only [h2, h531, h532, h534, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h4, h528, h533, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h0, h4, h528, h532, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h4, h520, h524, h529, h531, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h4, h520, h523, h524, h525, h528, h530, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h4, h522, h525, h528, h529, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h4, h521, h528, hc12, hc23, hlam, hphi]
                    · linarith only [h4, h520, h527, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
                  · linarith only [h4, h521, h544, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h547 | h547
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h549 | h549
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h550 | h550
                            · linarith only [h2, h524, h550, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h552 | h552
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h553 | h553
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h554 | h554
                                  · linarith only [h2, h524, h546, h554, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h556 | h556
                                    · linarith only [h2, h524, h546, h552, h556, hlam]
                                    · rcases h1bigk with h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [hlam, p558_0]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h547, h552, h554, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p558_1, u3ehi3]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h544, h547, h552, h554, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p558_1, u3ehi3]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        rcases p558_3 (m.d 0 1) (by simp) with h562 | h562
                                        · rcases p558_3 (m.d 1 2) (by simp) with h563 | h563
                                          · linarith only [h0, h563, hlam]
                                          · linarith only [h546, h563, hlam]
                                        · linarith only [h562, hlam, p558_0]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        rcases p558_3 (m.d 0 1) (by simp) with h567 | h567
                                        · rcases p558_3 (m.d 1 2) (by simp) with h568 | h568
                                          · linarith only [h0, h568, hlam]
                                          · linarith only [h547, h568, hlam]
                                        · linarith only [h567, hlam, p558_0]
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
                                        linarith only [h544, hlam, p558_0]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h0, h4, h546, h552, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p558_1, u3ehi3]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h0, h4, h546, h550, h552, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p558_1, u3ehi3]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h1, hlam, p558_0]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h1, h546, h552, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p558_1, u3ehi3]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [hlam, p558_0]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h1, h546, h552, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p558_1, u3ehi3]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h1, h546, h550, h552, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p558_1, u3ehi3]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h2, hlam, p558_0]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h546, hlam, p558_1]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h548, hlam, p558_0]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [hlam, p558_0]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h550, hlam, p558_1]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h3, hlam, p558_0]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h547, hlam, p558_1]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h549, hlam, p558_0]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [h3, h546, h552, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p558_1, u3ehi3]
                                      · have p558_0 := h558c.1
                                        have p558_1 := h558c.2.1
                                        have p558_2 := h558c.2.2.1
                                        have p558_3 := h558c.2.2.2
                                        linarith only [hlam, p558_0]
                                · linarith only [h0, h4, h547, h553, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h0, h4, h547, h552, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h4, h521, h523, h544, h547, h549, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h4, h522, h544, h547, h548, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h4, h521, h547, hc12, hc23, hlam, hphi]
                    · linarith only [h4, h520, h546, hc12, hc23, hlam, hphi]
              · linarith only [h522, h523, hc35, hlam, hphi, u3ehi3]
            · linarith only [h4, h520, h522, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h600 | h600
            · rcases m.htr 0 3 5 (by decide) (by decide) with h601 | h601
              · rcases m.htr 0 4 5 (by decide) (by decide) with h602 | h602
                · linarith only [h520, h521, h602, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
                  · linarith only [h0, h4, h604, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h606 | h606
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h607 | h607
                      · linarith only [h0, h521, h607, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h609 | h609
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h610 | h610
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h611 | h611
                            · linarith only [h2, h602, h611, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h614 | h614
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h615 | h615
                                  · linarith only [h0, h521, h602, h606, h615, hlam]
                                  · linarith only [h0, h521, h606, h613, h615, hc45, hlam, hphi, ht34, u3ehi3]
                                · linarith only [h1, h610, h614, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                              · linarith only [h0, h2, h4, h606, h609, h613, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h609, h610, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h600, h602, h609, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h520, h521, h606, hc12, hc25, hlam, hphi]
              · linarith only [h600, h601, hc35, hlam, hphi, u3ehi3]
            · linarith only [h4, h520, h600, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h625 | h625
          · rcases m.htr 0 3 4 (by decide) (by decide) with h626 | h626
            · rcases m.htr 0 3 5 (by decide) (by decide) with h627 | h627
              · rcases m.htr 0 4 5 (by decide) (by decide) with h628 | h628
                · rcases m.htr 1 2 3 (by decide) (by decide) with h629 | h629
                  · linarith only [h0, h4, h629, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h631 | h631
                    · linarith only [h520, h625, h629, h631, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h633 | h633
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h634 | h634
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h635 | h635
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h636 | h636
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h637 | h637
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h638 | h638
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h639 | h639
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h640 | h640
                                    · linarith only [h1, h634, h640, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h1, h634, h636, h640, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h2, h520, h636, h639, hlam]
                                · linarith only [h0, h4, h633, h638, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h0, h4, h633, h637, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h628, h631, h633, h636, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h634, h635, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h4, h626, h629, h633, h634, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h4, h625, h633, hc12, hc23, hlam, hphi]
                · linarith only [h520, h625, h628, hlam]
              · linarith only [h626, h627, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h652 | h652
              · linarith only [h626, h652, hc34, hlam, hphi, u3ehi4]
              · linarith only [h4, h625, h652, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h655 | h655
            · rcases m.htr 0 3 5 (by decide) (by decide) with h656 | h656
              · rcases m.htr 0 4 5 (by decide) (by decide) with h657 | h657
                · rcases m.htr 1 2 3 (by decide) (by decide) with h658 | h658
                  · linarith only [h0, h4, h658, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h660 | h660
                    · linarith only [h0, h520, h660, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h662 | h662
                      · linarith only [h0, h625, h662, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h664 | h664
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h665 | h665
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h666 | h666
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h667 | h667
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h668 | h668
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h669 | h669
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h670 | h670
                                    · linarith only [h1, h664, h670, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h2, h666, h670, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h2, h520, h666, h669, hlam]
                                · linarith only [h4, h655, h668, hc35, hlam, hphi, u3ehi3]
                              · linarith only [h1, h4, h664, h667, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h676 | h676
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h677 | h677
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h678 | h678
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h679 | h679
                                    · linarith only [h664, h666, h679, hlam]
                                    · rcases h1bigk with h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        rcases p681_3 (m.d 0 1) (by simp) with h683 | h683
                                        · rcases p681_3 (m.d 1 2) (by simp) with h684 | h684
                                          · linarith only [h684, hlam, p681_0]
                                          · rcases p681_3 (m.d 1 3) (by simp) with h686 | h686
                                            · linarith only [h1, h686, hlam]
                                            · linarith only [h658, h686, hlam]
                                        · linarith only [h683, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h665, hc01, hlam, hphi, ht0b, ht5b, p681_1, u5ehi3]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        rcases p681_3 (m.d 0 1) (by simp) with h691 | h691
                                        · rcases p681_3 (m.d 1 2) (by simp) with h692 | h692
                                          · linarith only [h0, h692, hlam]
                                          · rcases p681_3 (m.d 1 3) (by simp) with h694 | h694
                                            · linarith only [h1, h694, hlam]
                                            · linarith only [h664, h694, hlam]
                                        · linarith only [h691, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        rcases p681_3 (m.d 0 1) (by simp) with h698 | h698
                                        · rcases p681_3 (m.d 1 2) (by simp) with h699 | h699
                                          · linarith only [h0, h699, hlam]
                                          · rcases p681_3 (m.d 1 3) (by simp) with h701 | h701
                                            · linarith only [h1, h701, hlam]
                                            · linarith only [h665, h701, hlam]
                                        · linarith only [h698, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h0, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h658, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h660, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h662, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h1, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        rcases p681_3 (m.d 0 1) (by simp) with h711 | h711
                                        · rcases p681_3 (m.d 1 2) (by simp) with h712 | h712
                                          · linarith only [h658, h712, hlam]
                                          · rcases p681_3 (m.d 1 3) (by simp) with h714 | h714
                                            · rcases p681_3 (m.d 1 4) (by simp) with h715 | h715
                                              · linarith only [h664, h715, hlam]
                                              · linarith only [h660, h715, hlam]
                                            · linarith only [h658, h714, hlam]
                                        · linarith only [h0, h711, hlam]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h1, h664, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p681_1, u3ehi3]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p681_1, u5ehi1]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h2, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h655, h657, h666, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p681_1]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h664, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h666, hlam, p681_1]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h3, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h4, h655, h657, h666, hc12, hc23, hlam, hphi, p681_1]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h665, hlam, p681_0]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [h4, h655, h657, h664, h666, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p681_1, u3ehi3]
                                      · have p681_0 := h681c.1
                                        have p681_1 := h681c.2.1
                                        have p681_2 := h681c.2.2.1
                                        have p681_3 := h681c.2.2.2
                                        linarith only [hlam, p681_0]
                                  · linarith only [h520, h657, h678, hlam]
                                · linarith only [h4, h655, h677, hc35, hlam, hphi, u3ehi3]
                              · linarith only [h4, h655, h657, h664, h666, h676, hlam]
                          · linarith only [h4, h656, h664, h665, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h737 | h737
                          · linarith only [h4, h655, h664, h737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h739 | h739
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h740 | h740
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h741 | h741
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h742 | h742
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h743 | h743
                                    · rcases h1bigk with h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        rcases p744_3 (m.d 0 1) (by simp) with h746 | h746
                                        · rcases p744_3 (m.d 1 2) (by simp) with h747 | h747
                                          · linarith only [h747, hlam, p744_0]
                                          · rcases p744_3 (m.d 1 3) (by simp) with h749 | h749
                                            · linarith only [h1, h749, hlam]
                                            · linarith only [h658, h749, hlam]
                                        · linarith only [h746, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        rcases p744_3 (m.d 0 1) (by simp) with h753 | h753
                                        · rcases p744_3 (m.d 1 2) (by simp) with h754 | h754
                                          · linarith only [h0, h754, hlam]
                                          · rcases p744_3 (m.d 1 3) (by simp) with h756 | h756
                                            · linarith only [h756, hlam, p744_0]
                                            · rcases p744_3 (m.d 1 4) (by simp) with h758 | h758
                                              · linarith only [h2, h758, hlam]
                                              · linarith only [h664, h758, hlam]
                                        · linarith only [h753, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h739, hc01, hlam, hphi, ht0b, ht5b, p744_1, u5ehi4]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        rcases p744_3 (m.d 0 1) (by simp) with h763 | h763
                                        · rcases p744_3 (m.d 1 2) (by simp) with h764 | h764
                                          · linarith only [h0, h764, hlam]
                                          · rcases p744_3 (m.d 1 3) (by simp) with h766 | h766
                                            · linarith only [h1, h766, hlam]
                                            · rcases p744_3 (m.d 1 4) (by simp) with h768 | h768
                                              · linarith only [h2, h768, hlam]
                                              · linarith only [h739, h768, hlam]
                                        · linarith only [h763, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h0, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h658, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h660, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h662, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h1, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h4, h655, h737, h743, hc12, hc23, hlam, hphi, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h664, hlam, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h737, hlam, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h2, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h4, h655, h664, hc12, hc23, hlam, hphi, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h4, h655, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p744_1, u3ehi1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h4, h655, h664, h737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p744_1, u3ehi1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h3, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h4, h655, h737, h743, hc12, hc23, hlam, hphi, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h4, h655, h737, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p744_1, u3ehi1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h739, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [hlam, p744_0]
                                    · linarith only [h4, h655, h657, h664, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h2, h520, h657, h739, h742, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                                · linarith only [h4, h655, h664, h739, h741, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · linarith only [h4, h655, h740, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h796 | h796
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h797 | h797
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h798 | h798
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h799 | h799
                                    · linarith only [h664, h739, h799, hc34, hlam, hphi, u3ehi1]
                                    · linarith only [h4, h655, h657, h664, h799, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h520, h657, h798, hlam]
                                · linarith only [h4, h655, h664, h797, hc35, hlam, hphi, u3ehi1]
                              · linarith only [h4, h655, h657, h664, h739, h796, hc34, hlam, hphi, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h805 | h805
                  · linarith only [h0, h4, h805, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h807 | h807
                    · linarith only [h0, h520, h807, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h809 | h809
                      · linarith only [h0, h625, h809, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h811 | h811
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h812 | h812
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h813 | h813
                            · linarith only [h2, h657, h813, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h815 | h815
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h816 | h816
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h817 | h817
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h818 | h818
                                    · linarith only [h2, h657, h811, h818, hlam]
                                    · rcases h1bigk with h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        rcases p820_3 (m.d 0 1) (by simp) with h822 | h822
                                        · rcases p820_3 (m.d 1 2) (by simp) with h823 | h823
                                          · linarith only [h823, hlam, p820_0]
                                          · rcases p820_3 (m.d 1 3) (by simp) with h825 | h825
                                            · linarith only [h1, h825, hlam]
                                            · linarith only [h805, h825, hlam]
                                        · linarith only [h822, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h811, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p820_1, u3ehi3]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        rcases p820_3 (m.d 0 1) (by simp) with h830 | h830
                                        · rcases p820_3 (m.d 1 2) (by simp) with h831 | h831
                                          · linarith only [h0, h831, hlam]
                                          · rcases p820_3 (m.d 1 3) (by simp) with h833 | h833
                                            · linarith only [h1, h833, hlam]
                                            · linarith only [h811, h833, hlam]
                                        · linarith only [h830, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        rcases p820_3 (m.d 0 1) (by simp) with h837 | h837
                                        · rcases p820_3 (m.d 1 2) (by simp) with h838 | h838
                                          · linarith only [h0, h838, hlam]
                                          · rcases p820_3 (m.d 1 3) (by simp) with h840 | h840
                                            · linarith only [h1, h840, hlam]
                                            · linarith only [h812, h840, hlam]
                                        · linarith only [h837, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h0, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h805, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h807, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h809, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h1, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        rcases p820_3 (m.d 0 1) (by simp) with h850 | h850
                                        · rcases p820_3 (m.d 1 2) (by simp) with h851 | h851
                                          · linarith only [h805, h851, hlam]
                                          · rcases p820_3 (m.d 1 3) (by simp) with h853 | h853
                                            · rcases p820_3 (m.d 1 4) (by simp) with h854 | h854
                                              · linarith only [h811, h854, hlam]
                                              · linarith only [h807, h854, hlam]
                                            · linarith only [h805, h853, hlam]
                                        · linarith only [h0, h850, hlam]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h1, h811, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p820_1, u3ehi3]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h1, h811, h813, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p820_1, u3ehi3]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h2, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h2, h657, h817, hc12, hc25, hlam, hphi, p820_1]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h811, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h813, hlam, p820_1]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h3, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h3, h657, h815, h817, hc12, hc23, hlam, hphi, p820_1]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h812, hlam, p820_0]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [h3, h657, h811, h815, h817, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p820_1, u3ehi3]
                                      · have p820_0 := h820c.1
                                        have p820_1 := h820c.2.1
                                        have p820_2 := h820c.2.2.1
                                        have p820_3 := h820c.2.2.2
                                        linarith only [hlam, p820_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h872 | h872
                                    · linarith only [h0, h520, h817, h872, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h1bigk with h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c | h874c
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        rcases p874_3 (m.d 0 1) (by simp) with h876 | h876
                                        · rcases p874_3 (m.d 1 2) (by simp) with h877 | h877
                                          · linarith only [h877, hlam, p874_0]
                                          · rcases p874_3 (m.d 1 3) (by simp) with h879 | h879
                                            · linarith only [h1, h879, hlam]
                                            · linarith only [h805, h879, hlam]
                                        · linarith only [h876, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h811, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p874_1, u3ehi3]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        rcases p874_3 (m.d 0 1) (by simp) with h884 | h884
                                        · rcases p874_3 (m.d 1 2) (by simp) with h885 | h885
                                          · linarith only [h0, h885, hlam]
                                          · rcases p874_3 (m.d 1 3) (by simp) with h887 | h887
                                            · linarith only [h1, h887, hlam]
                                            · linarith only [h811, h887, hlam]
                                        · linarith only [h884, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        rcases p874_3 (m.d 0 1) (by simp) with h891 | h891
                                        · rcases p874_3 (m.d 1 2) (by simp) with h892 | h892
                                          · linarith only [h0, h892, hlam]
                                          · rcases p874_3 (m.d 1 3) (by simp) with h894 | h894
                                            · linarith only [h1, h894, hlam]
                                            · linarith only [h812, h894, hlam]
                                        · linarith only [h891, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h0, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h805, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h807, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h809, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h1, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        rcases p874_3 (m.d 0 1) (by simp) with h904 | h904
                                        · rcases p874_3 (m.d 1 2) (by simp) with h905 | h905
                                          · linarith only [h805, h905, hlam]
                                          · rcases p874_3 (m.d 1 3) (by simp) with h907 | h907
                                            · rcases p874_3 (m.d 1 4) (by simp) with h908 | h908
                                              · linarith only [h811, h908, hlam]
                                              · linarith only [h807, h908, hlam]
                                            · linarith only [h805, h907, hlam]
                                        · linarith only [h0, h904, hlam]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h1, h811, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p874_1, u3ehi3]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p874_1, u5ehi1]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h2, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h2, h520, h817, hc12, hc45, hlam, hphi, ht23, ht34, p874_1]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h811, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h813, hlam, p874_1]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h3, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        rcases p874_3 (m.d 0 1) (by simp) with h922 | h922
                                        · rcases p874_3 (m.d 1 2) (by simp) with h923 | h923
                                          · linarith only [h809, h923, hlam]
                                          · rcases p874_3 (m.d 1 3) (by simp) with h925 | h925
                                            · rcases p874_3 (m.d 1 4) (by simp) with h926 | h926
                                              · linarith only [h813, h926, hlam]
                                              · linarith only [h807, h926, hlam]
                                            · linarith only [h805, h925, hlam]
                                        · linarith only [h0, h922, hlam]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h812, hlam, p874_0]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [h3, h811, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p874_1, u3ehi3]
                                      · have p874_0 := h874c.1
                                        have p874_1 := h874c.2.1
                                        have p874_2 := h874c.2.2.1
                                        have p874_3 := h874c.2.2.2
                                        linarith only [hlam, p874_0]
                                · linarith only [h4, h655, h816, hc35, hlam, hphi, u3ehi3]
                              · linarith only [h1, h4, h811, h815, hlam]
                          · linarith only [h811, h812, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h655, h657, h811, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h655, h656, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h939 | h939
              · linarith only [h655, h939, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h941 | h941
                · rcases m.htr 1 2 3 (by decide) (by decide) with h942 | h942
                  · linarith only [h0, h4, h942, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h944 | h944
                    · linarith only [h0, h520, h944, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h946 | h946
                      · linarith only [h0, h625, h946, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h948 | h948
                        · linarith only [h1, h939, h948, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h950 | h950
                          · linarith only [h1, h939, h950, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h952 | h952
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h953 | h953
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h954 | h954
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h955 | h955
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h956 | h956
                                    · rcases h1bigk with h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        rcases p957_3 (m.d 0 1) (by simp) with h959 | h959
                                        · rcases p957_3 (m.d 1 2) (by simp) with h960 | h960
                                          · linarith only [h960, hlam, p957_0]
                                          · rcases p957_3 (m.d 1 3) (by simp) with h962 | h962
                                            · linarith only [h1, h962, hlam]
                                            · linarith only [h942, h962, hlam]
                                        · linarith only [h959, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        rcases p957_3 (m.d 0 1) (by simp) with h966 | h966
                                        · rcases p957_3 (m.d 1 2) (by simp) with h967 | h967
                                          · linarith only [h0, h967, hlam]
                                          · rcases p957_3 (m.d 1 3) (by simp) with h969 | h969
                                            · linarith only [h969, hlam, p957_0]
                                            · rcases p957_3 (m.d 1 4) (by simp) with h971 | h971
                                              · linarith only [h2, h971, hlam]
                                              · linarith only [h948, h971, hlam]
                                        · linarith only [h966, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h952, hc01, hlam, hphi, ht0b, ht5b, p957_1, u5ehi4]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        rcases p957_3 (m.d 0 1) (by simp) with h976 | h976
                                        · rcases p957_3 (m.d 1 2) (by simp) with h977 | h977
                                          · linarith only [h0, h977, hlam]
                                          · rcases p957_3 (m.d 1 3) (by simp) with h979 | h979
                                            · linarith only [h1, h979, hlam]
                                            · rcases p957_3 (m.d 1 4) (by simp) with h981 | h981
                                              · linarith only [h2, h981, hlam]
                                              · linarith only [h952, h981, hlam]
                                        · linarith only [h976, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h0, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h942, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h944, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h946, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h1, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h1, h939, h953, h956, hc12, hc23, hlam, hphi, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h948, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h950, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h2, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h2, h655, h953, hc12, hc23, hlam, hphi, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h2, h655, h953, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p957_1, u3ehi1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h2, h655, h953, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p957_1, u5ehi1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h3, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h3, h939, h953, h956, hc12, hc23, hlam, hphi, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h3, h939, h953, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p957_1, u3ehi1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h952, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hlam, p957_0]
                                    · linarith only [h1, h655, h956, hc45, hlam, hphi, ht34, u3ehi1]
                                  · linarith only [h1, h2, h655, h952, h953, h955, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                · linarith only [h2, h655, h952, h953, h954, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1008 | h1008
                                · linarith only [h1008, h953, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1010 | h1010
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1011 | h1011
                                    · rcases h1bigk with h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        rcases p1012_3 (m.d 0 1) (by simp) with h1014 | h1014
                                        · rcases p1012_3 (m.d 1 2) (by simp) with h1015 | h1015
                                          · linarith only [h1015, hlam, p1012_0]
                                          · rcases p1012_3 (m.d 1 3) (by simp) with h1017 | h1017
                                            · linarith only [h1, h1017, hlam]
                                            · linarith only [h1017, h942, hlam]
                                        · linarith only [h1014, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        rcases p1012_3 (m.d 0 1) (by simp) with h1021 | h1021
                                        · rcases p1012_3 (m.d 1 2) (by simp) with h1022 | h1022
                                          · linarith only [h0, h1022, hlam]
                                          · rcases p1012_3 (m.d 1 3) (by simp) with h1024 | h1024
                                            · linarith only [h1024, hlam, p1012_0]
                                            · rcases p1012_3 (m.d 1 4) (by simp) with h1026 | h1026
                                              · linarith only [h1026, h2, hlam]
                                              · linarith only [h1026, h948, hlam]
                                        · linarith only [h1021, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h952, hc01, hlam, hphi, ht0b, ht5b, p1012_1, u5ehi4]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        rcases p1012_3 (m.d 0 1) (by simp) with h1031 | h1031
                                        · rcases p1012_3 (m.d 1 2) (by simp) with h1032 | h1032
                                          · linarith only [h0, h1032, hlam]
                                          · rcases p1012_3 (m.d 1 3) (by simp) with h1034 | h1034
                                            · linarith only [h1, h1034, hlam]
                                            · rcases p1012_3 (m.d 1 4) (by simp) with h1036 | h1036
                                              · linarith only [h1036, h2, hlam]
                                              · linarith only [h1036, h952, hlam]
                                        · linarith only [h1031, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h0, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h942, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h944, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h946, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h1, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h1, h1008, h1011, h4, hc12, hc34, hlam, hphi, ht23, p1012_1]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h948, hlam, p1012_1]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h950, hlam, p1012_1]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h2, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        rcases p1012_3 (m.d 0 1) (by simp) with h1051 | h1051
                                        · rcases p1012_3 (m.d 1 2) (by simp) with h1052 | h1052
                                          · linarith only [h1052, h944, hlam]
                                          · rcases p1012_3 (m.d 1 3) (by simp) with h1054 | h1054
                                            · linarith only [h1054, h948, hlam]
                                            · linarith only [h1054, h942, hlam]
                                        · linarith only [h0, h1051, hlam]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1012_1, u3ehi1]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p1012_1, u5ehi1]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h3, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        rcases p1012_3 (m.d 0 1) (by simp) with h1062 | h1062
                                        · rcases p1012_3 (m.d 1 2) (by simp) with h1063 | h1063
                                          · linarith only [h1063, h946, hlam]
                                          · rcases p1012_3 (m.d 1 3) (by simp) with h1065 | h1065
                                            · linarith only [h1065, h950, hlam]
                                            · linarith only [h1065, h942, hlam]
                                        · linarith only [h0, h1062, hlam]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1012_1, u3ehi1]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [h952, hlam, p1012_0]
                                      · have p1012_0 := h1012c.1
                                        have p1012_1 := h1012c.2.1
                                        have p1012_2 := h1012c.2.2.1
                                        have p1012_3 := h1012c.2.2.2
                                        linarith only [hlam, p1012_0]
                                    · linarith only [h1011, h655, hc45, hlam, hphi, ht34, u3ehi0]
                                  · linarith only [h1010, h2, h520, h941, h952, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                            · linarith only [h655, h941, h948, h952, hc34, hlam, hphi, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1075 | h1075
                  · linarith only [h0, h1075, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1077 | h1077
                    · linarith only [h0, h1077, h520, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1079 | h1079
                      · linarith only [h0, h1079, h625, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1081 | h1081
                        · linarith only [h1, h1081, h939, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1083 | h1083
                          · linarith only [h1, h1083, h939, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1085 | h1085
                            · linarith only [h1085, h2, h655, h941, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1087 | h1087
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1088 | h1088
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1089 | h1089
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1090 | h1090
                                    · linarith only [h1, h1090, h655, h941, hc34, hlam, hphi, u3ehi1]
                                    · linarith only [h1, h1087, h1089, h1090, h655, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h1, h1087, h1089, h655, hc45, hlam, hphi, ht34, u3ehi1]
                                · linarith only [h1, h1087, h1088, h655, hc35, hlam, hphi, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1095 | h1095
                                · linarith only [h1087, h1095, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1097 | h1097
                                  · linarith only [h1, h1087, h1097, h655, h941, hc34, hlam, hphi, u3ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1099 | h1099
                                    · linarith only [h1087, h1097, h1099, h4, hc02, hc34, hlam, hphi, ht23]
                                    · linarith only [h1, h1099, h655, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1102 | h1102
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1103 | h1103
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1104 | h1104
          · linarith only [h0, h1104, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1106 | h1106
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1107 | h1107
              · linarith only [h0, h1102, h1107, h3, hlam]
              · linarith only [h1106, h1107, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1110 | h1110
              · linarith only [h1106, h1110, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1112 | h1112
                · linarith only [h0, h1103, h1112, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1114 | h1114
                  · linarith only [h0, h1114, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h1102, h1104, h1114, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1117 | h1117
          · linarith only [h1103, h1117, h2, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1119 | h1119
            · linarith only [h1102, h1103, h1119, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1121 | h1121
              · linarith only [h1119, h1121, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1123 | h1123
                · linarith only [h1123, h2, h3, hlam]
                · linarith only [h1102, h1103, h1123, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1126 | h1126
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1127 | h1127
          · linarith only [h0, h1127, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1129 | h1129
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1130 | h1130
              · linarith only [h1, h1130, h3, hlam]
              · linarith only [h1129, h1130, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1102, h1126, h1129, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1134 | h1134
          · linarith only [h0, h1134, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1136 | h1136
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1137 | h1137
              · linarith only [h1, h1137, h3, hlam]
              · linarith only [h1136, h1137, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1140 | h1140
              · linarith only [h1136, h1140, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1142 | h1142
                · linarith only [h1142, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1144 | h1144
                  · linarith only [h0, h1102, h1136, h1142, h1144, hc45, hlam, hphi, ht34, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1146 | h1146
                    · linarith only [h1, h1126, h1144, h1146, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1148 | h1148
                      · linarith only [h0, h1134, h1148, h3, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1150 | h1150
                        · linarith only [h1, h1148, h1150, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1152 | h1152
                          · linarith only [h1, h1136, h1152, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h1150, h1152, h2, h3, hc35, hlam, hphi, u3ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1155 | h1155
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1156 | h1156
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1157 | h1157
        · linarith only [h0, h1157, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1159 | h1159
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1160 | h1160
            · linarith only [h0, h1156, h1160, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1162 | h1162
              · linarith only [h1160, h1162, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1164 | h1164
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1165 | h1165
                  · linarith only [h0, h1165, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h1156, h1157, h1165, hc12, hc24, hlam, hphi]
                · linarith only [h0, h1156, h1164, h2, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1169 | h1169
            · linarith only [h1155, h1156, h1159, h1169, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1171 | h1171
              · linarith only [h1169, h1171, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1173 | h1173
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1174 | h1174
                  · linarith only [h0, h1174, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h1156, h1157, h1174, hc12, hc24, hlam, hphi]
                · linarith only [h1155, h1156, h1159, h1173, h2, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1178 | h1178
        · linarith only [h0, h1178, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1180 | h1180
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1181 | h1181
            · linarith only [h1, h1181, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1183 | h1183
              · linarith only [h1181, h1183, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1156, h1180, h1183, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1186 | h1186
            · linarith only [h1, h1186, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1188 | h1188
              · linarith only [h1186, h1188, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1190 | h1190
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1191 | h1191
                  · linarith only [h0, h1156, h1191, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1193 | h1193
                    · linarith only [h0, h1178, h1193, h2, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1195 | h1195
                      · linarith only [h1, h1180, h1191, h1193, h1195, h2, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1197 | h1197
                        · linarith only [h1, h1186, h1193, h1197, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1, h1197, h2, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h1190, h2, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1201 | h1201
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1202 | h1202
        · linarith only [h0, h1202, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1204 | h1204
          · linarith only [h0, h1155, h1204, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1206 | h1206
            · linarith only [h0, h1201, h1206, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1208 | h1208
              · linarith only [h1206, h1208, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1210 | h1210
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1211 | h1211
                  · linarith only [h0, h1211, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h1201, h1202, h1211, hc12, hc24, hlam, hphi]
                · linarith only [h0, h1201, h1210, h2, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1215 | h1215
        · linarith only [h1, h1201, h1215, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1217 | h1217
          · linarith only [h1, h1155, h1201, h1217, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1219 | h1219
            · linarith only [h1, h1219, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1221 | h1221
              · linarith only [h1219, h1221, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1223 | h1223
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1224 | h1224
                  · linarith only [h0, h1201, h1224, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1226 | h1226
                    · linarith only [h0, h1155, h1215, h1223, h1226, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1228 | h1228
                      · linarith only [h1, h1217, h1224, h1226, h1228, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1230 | h1230
                        · linarith only [h1, h1219, h1226, h1230, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1, h1230, h2, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h1223, h2, hc45, hlam, hphi, ht34, u3ehi1]

end R2N4
