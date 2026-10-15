import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4108000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_R_H_I_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
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
                        · linarith only [h0, h13, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h10, h13, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h16, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h10, h16, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h10, h11, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h10, h20, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                        · linarith only [h0, h10, h23, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                          · linarith only [h20, h25, h7, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                              · rcases h2bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi2]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 2) (by simp) with h32 | h32
                                  · rcases p29_3 (m.d 1 2) (by simp) with h33 | h33
                                    · linarith only [h0, h33, hlam]
                                    · linarith only [h33, h7, hlam]
                                  · linarith only [h32, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 2) (by simp) with h37 | h37
                                  · rcases p29_3 (m.d 1 2) (by simp) with h38 | h38
                                    · linarith only [h0, h38, hlam]
                                    · linarith only [h38, h8, hlam]
                                  · linarith only [h37, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 2) (by simp) with h42 | h42
                                  · rcases p29_3 (m.d 1 2) (by simp) with h43 | h43
                                    · linarith only [h0, h43, hlam]
                                    · linarith only [h43, h9, hlam]
                                  · linarith only [h42, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi2]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h27, hc01, hc45, hlam, hphi, ht0b, ht5b, p29_1]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h25, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi2]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h3, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h7, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h23, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h25, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h4, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h8, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi2]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h25, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi2]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h5, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h9, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi2]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h27, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                              · linarith only [h10, h28, h7, hc45, hlam, hphi, ht34, u3ehi2]
                            · linarith only [h0, h22, h23, h27, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                        · linarith only [h10, h69, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                          · linarith only [h10, h7, h71, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h73 | h73
                            · linarith only [h0, h10, h22, h4, h73, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                              · linarith only [h10, h22, h7, h75, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h10, h7, h75, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h5, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h4, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
              · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
                · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                        · linarith only [h0, h3, h7, h80, h85, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h7, h80, h82, h85, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                        · linarith only [h0, h3, h7, h80, h88, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h7, h81, h83, h88, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h82, h83, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h7, h80, h82, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                      · linarith only [h80, h81, h95, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                        · linarith only [h0, h3, h7, h80, h97, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h7, h80, h93, h97, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h93, h94, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h7, h80, h93, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h105 | h105
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                          · linarith only [h0, h102, h107, h4, h80, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h103, h107, h7, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h102, h103, h104, h106, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h102, h105, h80, hlam]
                    · linarith only [h103, h104, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                    · linarith only [h103, h113, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h102, h113, h7, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                              · rcases h2bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h125 | h125
                                  · rcases p123_3 (m.d 1 2) (by simp) with h126 | h126
                                    · linarith only [h0, h126, hlam]
                                    · rcases p123_3 (m.d 2 3) (by simp) with h128 | h128
                                      · linarith only [h128, h3, hlam]
                                      · linarith only [h128, h7, hlam]
                                  · linarith only [h0, h125, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, h116, h122, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p123_1, u3ehi4]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h133 | h133
                                  · rcases p123_3 (m.d 1 2) (by simp) with h134 | h134
                                    · linarith only [h0, h134, hlam]
                                    · rcases p123_3 (m.d 2 3) (by simp) with h136 | h136
                                      · linarith only [h136, h3, hlam]
                                      · linarith only [h119, h136, hlam]
                                  · linarith only [h133, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h140 | h140
                                  · rcases p123_3 (m.d 1 2) (by simp) with h141 | h141
                                    · linarith only [h0, h141, hlam]
                                    · rcases p123_3 (m.d 2 3) (by simp) with h143 | h143
                                      · linarith only [h143, h3, hlam]
                                      · linarith only [h120, h143, hlam]
                                  · linarith only [h140, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h7, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h80, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h102, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h3, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h153 | h153
                                  · rcases p123_3 (m.d 1 2) (by simp) with h154 | h154
                                    · linarith only [h154, hlam, p123_0]
                                    · rcases p123_3 (m.d 2 3) (by simp) with h156 | h156
                                      · rcases p123_3 (m.d 2 4) (by simp) with h157 | h157
                                        · linarith only [h119, h157, hlam]
                                        · linarith only [h157, h80, hlam]
                                      · linarith only [h156, hlam, p123_0]
                                  · linarith only [h0, h153, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h102, h121, hc12, hc23, hlam, hphi, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, h102, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h4, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h166 | h166
                                  · rcases p123_3 (m.d 1 2) (by simp) with h167 | h167
                                    · linarith only [h167, hlam, p123_0]
                                    · rcases p123_3 (m.d 2 3) (by simp) with h169 | h169
                                      · rcases p123_3 (m.d 2 4) (by simp) with h170 | h170
                                        · rcases p123_3 (m.d 2 5) (by simp) with h171 | h171
                                          · linarith only [h121, h171, hlam]
                                          · linarith only [h102, h171, hlam]
                                        · linarith only [h170, hlam, p123_0]
                                      · linarith only [h169, h7, hlam]
                                  · linarith only [h0, h166, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h119, hlam, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, h102, h117, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p123_1, u3ehi4]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h5, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h181 | h181
                                  · rcases p123_3 (m.d 1 2) (by simp) with h182 | h182
                                    · linarith only [h182, hlam, p123_0]
                                    · rcases p123_3 (m.d 2 3) (by simp) with h184 | h184
                                      · rcases p123_3 (m.d 2 4) (by simp) with h185 | h185
                                        · rcases p123_3 (m.d 2 5) (by simp) with h186 | h186
                                          · rcases h5bigk with h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h0, h117, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p187_1, u3ehi4]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p123_1, p187_1]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p187_1, u3ehi4]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              rcases p187_3 (m.d 0 5) (by simp) with h192 | h192
                                              · rcases p187_3 (m.d 1 5) (by simp) with h193 | h193
                                                · linarith only [h193, h2, hlam]
                                                · linarith only [h118, h193, hlam]
                                              · linarith only [h192, h6, hlam]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h2, hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h102, hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p187_1, u3ehi4]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h1, h116, h118, hc01, hc45, hlam, hphi, ht0b, ht5b, p187_1]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h5, hlam, p187_1]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p187_1]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h0, h120, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p187_1, u3ehi4]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h0, h119, h121, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p187_1]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h117, hc15, hlam, hphi, ht01, p187_1, u0ehi4]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h117, hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h120, hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h0, h116, h122, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p187_1]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h6, hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h118, hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h121, hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [h122, hlam, p187_0]
                                            · have p187_0 := h187c.1
                                              have p187_1 := h187c.2.1
                                              have p187_2 := h187c.2.2.1
                                              have p187_3 := h187c.2.2.2
                                              linarith only [hlam, p187_0]
                                          · linarith only [h186, hlam, p123_0]
                                        · linarith only [h185, h80, hlam]
                                      · linarith only [h184, h7, hlam]
                                  · linarith only [h0, h181, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h120, hlam, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h121, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                              · linarith only [h0, h116, h118, h122, h3, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h116, h118, h121, h3, h7, h80, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h116, h120, h7, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h116, h119, h7, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h229 | h229
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h230 | h230
                            · linarith only [h0, h116, h118, h230, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h232 | h232
                              · linarith only [h1, h116, h230, h232, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h2bigk with h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h230, h4, h6, h80, hlam, p234_2]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h0, h117, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p234_1, u3ehi4]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  rcases p234_3 (m.d 0 2) (by simp) with h238 | h238
                                  · rcases p234_3 (m.d 1 2) (by simp) with h239 | h239
                                    · linarith only [h0, h239, hlam]
                                    · rcases p234_3 (m.d 2 3) (by simp) with h241 | h241
                                      · linarith only [h241, h3, hlam]
                                      · linarith only [h228, h241, hlam]
                                  · linarith only [h238, hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  rcases p234_3 (m.d 0 2) (by simp) with h245 | h245
                                  · rcases p234_3 (m.d 1 2) (by simp) with h246 | h246
                                    · linarith only [h0, h246, hlam]
                                    · rcases p234_3 (m.d 2 3) (by simp) with h248 | h248
                                      · linarith only [h248, h3, hlam]
                                      · linarith only [h229, h248, hlam]
                                  · linarith only [h245, hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h0, hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h7, hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h80, hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h102, hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h3, hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  rcases p234_3 (m.d 0 2) (by simp) with h258 | h258
                                  · rcases p234_3 (m.d 1 2) (by simp) with h259 | h259
                                    · linarith only [h259, hlam, p234_0]
                                    · rcases p234_3 (m.d 2 3) (by simp) with h261 | h261
                                      · rcases p234_3 (m.d 2 4) (by simp) with h262 | h262
                                        · linarith only [h228, h262, hlam]
                                        · linarith only [h262, h80, hlam]
                                      · linarith only [h261, hlam, p234_0]
                                  · linarith only [h0, h258, hlam]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h80, hc12, hc23, hlam, hphi, p234_1]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h0, h102, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p234_1]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h4, hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h0, h230, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p234_1]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h228, hlam, p234_1]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h230, hlam, p234_1]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h5, hlam, p234_0]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  rcases p234_3 (m.d 0 2) (by simp) with h276 | h276
                                  · rcases p234_3 (m.d 1 2) (by simp) with h277 | h277
                                    · linarith only [h277, hlam, p234_0]
                                    · rcases p234_3 (m.d 2 3) (by simp) with h279 | h279
                                      · rcases p234_3 (m.d 2 4) (by simp) with h280 | h280
                                        · linarith only [h230, h280, hlam]
                                        · linarith only [h280, h80, hlam]
                                      · linarith only [h279, h7, hlam]
                                  · linarith only [h0, h276, hlam]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h229, hlam, p234_1]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [h0, h5, h80, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p234_1]
                                · have p234_0 := h234c.1
                                  have p234_1 := h234c.2.1
                                  have p234_2 := h234c.2.2.1
                                  have p234_3 := h234c.2.2.2
                                  linarith only [hlam, p234_0]
                          · linarith only [h1, h117, h229, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h117, h228, h7, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h116, h117, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h291 | h291
                    · linarith only [h116, h291, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                        · linarith only [h0, h116, h294, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h296 | h296
                          · linarith only [h291, h294, h296, hc34, hlam, hphi, u3ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h298 | h298
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h299 | h299
                              · rcases h2bigk with h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  rcases p300_3 (m.d 0 2) (by simp) with h302 | h302
                                  · rcases p300_3 (m.d 1 2) (by simp) with h303 | h303
                                    · linarith only [h0, h303, hlam]
                                    · rcases p300_3 (m.d 2 3) (by simp) with h305 | h305
                                      · linarith only [h3, h305, hlam]
                                      · linarith only [h305, h7, hlam]
                                  · linarith only [h0, h302, hlam]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  rcases p300_3 (m.d 0 2) (by simp) with h309 | h309
                                  · rcases p300_3 (m.d 1 2) (by simp) with h310 | h310
                                    · linarith only [h0, h310, hlam]
                                    · rcases p300_3 (m.d 2 3) (by simp) with h312 | h312
                                      · linarith only [h312, hlam, p300_0]
                                      · rcases p300_3 (m.d 2 4) (by simp) with h314 | h314
                                        · linarith only [h314, h4, hlam]
                                        · linarith only [h294, h314, hlam]
                                  · linarith only [h309, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  rcases p300_3 (m.d 0 2) (by simp) with h318 | h318
                                  · rcases p300_3 (m.d 1 2) (by simp) with h319 | h319
                                    · linarith only [h0, h319, hlam]
                                    · rcases p300_3 (m.d 2 3) (by simp) with h321 | h321
                                      · linarith only [h3, h321, hlam]
                                      · rcases p300_3 (m.d 2 4) (by simp) with h323 | h323
                                        · linarith only [h323, hlam, p300_0]
                                        · rcases p300_3 (m.d 2 5) (by simp) with h325 | h325
                                          · linarith only [h325, h5, hlam]
                                          · rcases h5bigk with h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [hlam, p327_0]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h291, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1, u3ehi1]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h0, h296, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p327_1]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1, u3ehi4]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              rcases p327_3 (m.d 0 5) (by simp) with h332 | h332
                                              · rcases p327_3 (m.d 1 5) (by simp) with h333 | h333
                                                · linarith only [h2, h333, hlam]
                                                · linarith only [h293, h333, hlam]
                                              · linarith only [h332, h6, hlam]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h2, hlam, p327_0]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [hlam, p327_0]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h102, hlam, p327_0]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h291, hlam, p327_1]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p327_1]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h5, hlam, p327_1]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p327_1]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [hlam, p327_0]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h296, hlam, p327_1]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h0, h298, hc01, hc45, hlam, hphi, ht0b, ht5b, p300_1, p327_1]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p327_1, u0ehi4]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h291, hc35, hlam, hphi, p327_1, u3ehi1]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h102, h291, hc35, hlam, hphi, p327_1, u3ehi1]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [hlam, p327_0]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              rcases p327_3 (m.d 0 5) (by simp) with h351 | h351
                                              · rcases p327_3 (m.d 1 5) (by simp) with h352 | h352
                                                · linarith only [h291, h352, hlam]
                                                · linarith only [h293, h352, hlam]
                                              · linarith only [h351, h6, hlam]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h6, hlam, p327_0]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h293, hlam, p327_0]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h298, hlam, p327_0]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [h299, hlam, p327_0]
                                            · have p327_0 := h327c.1
                                              have p327_1 := h327c.2.1
                                              have p327_2 := h327c.2.2.1
                                              have p327_3 := h327c.2.2.2
                                              linarith only [hlam, p327_0]
                                  · linarith only [h318, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  rcases p300_3 (m.d 0 2) (by simp) with h362 | h362
                                  · rcases p300_3 (m.d 1 2) (by simp) with h363 | h363
                                    · linarith only [h0, h363, hlam]
                                    · rcases p300_3 (m.d 2 3) (by simp) with h365 | h365
                                      · linarith only [h3, h365, hlam]
                                      · rcases p300_3 (m.d 2 4) (by simp) with h367 | h367
                                        · linarith only [h367, h4, hlam]
                                        · linarith only [h298, h367, hlam]
                                  · linarith only [h362, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h0, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h7, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h80, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h102, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h3, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h294, hc12, hc34, hlam, hphi, ht23, p300_1]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h294, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h296, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h4, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  rcases p300_3 (m.d 0 2) (by simp) with h382 | h382
                                  · rcases p300_3 (m.d 1 2) (by simp) with h383 | h383
                                    · linarith only [h383, hlam, p300_0]
                                    · rcases p300_3 (m.d 2 3) (by simp) with h385 | h385
                                      · linarith only [h294, h385, hlam]
                                      · linarith only [h385, h7, hlam]
                                  · linarith only [h0, h382, hlam]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p300_1, u3ehi1]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h0, h296, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p300_1, u3ehi1]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h5, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  rcases p300_3 (m.d 0 2) (by simp) with h393 | h393
                                  · rcases p300_3 (m.d 1 2) (by simp) with h394 | h394
                                    · linarith only [h394, hlam, p300_0]
                                    · rcases p300_3 (m.d 2 3) (by simp) with h396 | h396
                                      · linarith only [h296, h396, hlam]
                                      · linarith only [h396, h7, hlam]
                                  · linarith only [h0, h393, hlam]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h0, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p300_1, u3ehi1]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h298, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [hlam, p300_0]
                              · linarith only [h116, h299, hc45, hlam, hphi, ht34, u3ehi1]
                            · linarith only [h293, h298, h80, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h405 | h405
                        · linarith only [h0, h116, h3, h405, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h407 | h407
                          · linarith only [h405, h407, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h409 | h409
                            · linarith only [h0, h116, h293, h4, h409, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h411 | h411
                              · linarith only [h405, h409, h411, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h0, h116, h4, h411, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h414 | h414
            · rcases m.htr 1 2 4 (by decide) (by decide) with h415 | h415
              · rcases m.htr 1 2 5 (by decide) (by decide) with h416 | h416
                · rcases m.htr 1 3 4 (by decide) (by decide) with h417 | h417
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h419 | h419
                      · linarith only [h419, h6, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                        · linarith only [h0, h414, h421, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h417, h421, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h417, h418, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h425 | h425
                    · linarith only [h417, h425, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h427 | h427
                      · linarith only [h427, h6, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h429 | h429
                        · linarith only [h0, h3, h417, h429, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h431 | h431
                          · linarith only [h414, h417, h431, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h433 | h433
                            · linarith only [h4, h433, h6, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h435 | h435
                              · linarith only [h435, h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                              · linarith only [h417, h435, hc45, hlam, hphi, ht34, u3ehi1]
                · linarith only [h0, h414, h416, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h4, h414, h415, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h440 | h440
              · rcases m.htr 1 2 5 (by decide) (by decide) with h441 | h441
                · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h443 | h443
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h444 | h444
                      · linarith only [h414, h440, h444, h6, hc23, hlam, hphi, ht01, ht12, u0ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                        · linarith only [h0, h3, h414, h440, h446, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h414, h441, h443, h446, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h442, h443, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h414, h440, h442, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h453 | h453
                      · linarith only [h440, h441, h453, h5, h6, hc05, hlam, hphi, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
                        · linarith only [h0, h3, h414, h440, h455, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h414, h440, h451, h455, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h451, h452, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h414, h440, h451, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h460 | h460
                · rcases m.htr 1 3 4 (by decide) (by decide) with h461 | h461
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h462 | h462
                    · linarith only [h4, h440, h460, h462, h6, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h461, h462, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h465 | h465
                    · linarith only [h4, h440, h461, h465, h6, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h4, h440, h460, h465, h6, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h468 | h468
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h469 | h469
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h470 | h470
                      · linarith only [h4, h440, h470, h6, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h472 | h472
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h473 | h473
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h474 | h474
                            · linarith only [h4, h474, h6, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h476 | h476
                              · linarith only [h4, h440, h468, h476, h6, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases h2bigk with h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  rcases p478_3 (m.d 0 2) (by simp) with h480 | h480
                                  · rcases p478_3 (m.d 1 2) (by simp) with h481 | h481
                                    · linarith only [h0, h481, hlam]
                                    · rcases p478_3 (m.d 2 3) (by simp) with h483 | h483
                                      · linarith only [h3, h483, hlam]
                                      · linarith only [h414, h483, hlam]
                                  · linarith only [h0, h480, hlam]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h0, h414, h469, h476, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p478_1, u3ehi3]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  rcases p478_3 (m.d 0 2) (by simp) with h488 | h488
                                  · rcases p478_3 (m.d 1 2) (by simp) with h489 | h489
                                    · linarith only [h0, h489, hlam]
                                    · rcases p478_3 (m.d 2 3) (by simp) with h491 | h491
                                      · linarith only [h3, h491, hlam]
                                      · linarith only [h472, h491, hlam]
                                  · linarith only [h488, hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  rcases p478_3 (m.d 0 2) (by simp) with h495 | h495
                                  · rcases p478_3 (m.d 1 2) (by simp) with h496 | h496
                                    · linarith only [h0, h496, hlam]
                                    · rcases p478_3 (m.d 2 3) (by simp) with h498 | h498
                                      · linarith only [h3, h498, hlam]
                                      · linarith only [h473, h498, hlam]
                                  · linarith only [h495, hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h0, hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h414, hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h440, hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h460, hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h3, hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  rcases p478_3 (m.d 0 2) (by simp) with h508 | h508
                                  · rcases p478_3 (m.d 1 2) (by simp) with h509 | h509
                                    · linarith only [h509, hlam, p478_0]
                                    · rcases p478_3 (m.d 2 3) (by simp) with h511 | h511
                                      · rcases p478_3 (m.d 2 4) (by simp) with h512 | h512
                                        · linarith only [h472, h512, hlam]
                                        · linarith only [h440, h512, hlam]
                                      · linarith only [h511, hlam, p478_0]
                                  · linarith only [h0, h508, hlam]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h440, hc12, hc23, hlam, hphi, p478_1]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h0, h3, h460, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p478_1]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h4, hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h4, h6, hc12, hc45, hlam, hphi, ht23, ht34, p478_1]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h472, hlam, p478_1]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h474, hlam, p478_1]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h5, hlam, p478_0]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  rcases p478_3 (m.d 0 2) (by simp) with h526 | h526
                                  · rcases p478_3 (m.d 1 2) (by simp) with h527 | h527
                                    · linarith only [h527, hlam, p478_0]
                                    · rcases p478_3 (m.d 2 3) (by simp) with h529 | h529
                                      · rcases p478_3 (m.d 2 4) (by simp) with h530 | h530
                                        · linarith only [h474, h530, hlam]
                                        · linarith only [h440, h530, hlam]
                                      · linarith only [h414, h529, hlam]
                                  · linarith only [h0, h526, hlam]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h473, hlam, p478_1]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [h440, hc12, hc25, hlam, hphi, p478_1]
                                · have p478_0 := h478c.1
                                  have p478_1 := h478c.2.1
                                  have p478_2 := h478c.2.2.1
                                  have p478_3 := h478c.2.2.2
                                  linarith only [hlam, p478_0]
                          · linarith only [h1, h469, h473, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h4, h414, h440, h468, h472, h6, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h468, h469, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h541 | h541
                    · linarith only [h4, h440, h468, h541, h6, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h543 | h543
                      · linarith only [h4, h440, h543, h6, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                        · linarith only [h0, h3, h468, h545, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h547 | h547
                          · linarith only [h4, h545, h547, h6, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h549 | h549
                            · linarith only [h4, h549, h6, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h551 | h551
                              · linarith only [h4, h545, h551, h6, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h468, h551, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h554 | h554
          · linarith only [h4, h5, h554, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h556 | h556
            · rcases m.htr 1 2 4 (by decide) (by decide) with h557 | h557
              · rcases m.htr 1 2 5 (by decide) (by decide) with h558 | h558
                · linarith only [h0, h5, h558, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h560 | h560
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h561 | h561
                    · linarith only [h556, h558, h561, hlam]
                    · linarith only [h560, h561, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h564 | h564
                    · linarith only [h560, h564, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h566 | h566
                      · linarith only [h0, h554, h557, h566, hc02, hlam, hphi, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
                        · linarith only [h3, h5, h568, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h570 | h570
                          · linarith only [h0, h5, h557, h564, h568, h570, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h3, h5, h570, hc35, hlam, hphi, u3ehi2]
              · linarith only [h4, h5, h556, h557, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h3, h5, h556, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h575 | h575
        · rcases m.htr 0 4 5 (by decide) (by decide) with h576 | h576
          · rcases m.htr 1 2 3 (by decide) (by decide) with h577 | h577
            · rcases m.htr 1 2 4 (by decide) (by decide) with h578 | h578
              · linarith only [h0, h4, h578, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h580 | h580
                · rcases m.htr 1 3 4 (by decide) (by decide) with h581 | h581
                  · linarith only [h577, h578, h581, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h583 | h583
                    · linarith only [h581, h583, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h585 | h585
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h586 | h586
                        · linarith only [h577, h581, h586, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h3, h4, h586, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h576, h577, h578, h585, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h4, h575, h577, h580, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h3, h4, h577, hc12, hc24, hlam, hphi]
          · linarith only [h3, h4, h576, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h593 | h593
          · rcases m.htr 1 2 3 (by decide) (by decide) with h594 | h594
            · rcases m.htr 1 2 4 (by decide) (by decide) with h595 | h595
              · linarith only [h0, h4, h595, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h597 | h597
                · linarith only [h0, h575, h597, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h599 | h599
                  · linarith only [h594, h595, h599, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h601 | h601
                    · linarith only [h599, h601, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h603 | h603
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
                        · linarith only [h594, h599, h604, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h3, h4, h604, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h593, h594, h595, h603, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h3, h575, h594, hc12, hc25, hlam, hphi]
          · linarith only [h3, h4, h593, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h610 | h610
      · rcases m.htr 0 2 5 (by decide) (by decide) with h611 | h611
        · rcases m.htr 0 4 5 (by decide) (by decide) with h612 | h612
          · rcases m.htr 1 2 3 (by decide) (by decide) with h613 | h613
            · linarith only [h3, h610, h612, h613, hc12, hlam, hphi, ht01, u0ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h615 | h615
              · rcases m.htr 1 2 5 (by decide) (by decide) with h616 | h616
                · rcases m.htr 1 3 4 (by decide) (by decide) with h617 | h617
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h618 | h618
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h619 | h619
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h620 | h620
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h621 | h621
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h622 | h622
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h623 | h623
                              · rcases h2bigk with h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h3, h615, h621, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p624_1, u3ehi4]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h3, hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h3, h621, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p624_1, u3ehi4]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h3, h621, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p624_1, u3ehi4]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h0, hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h613, hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h0, h621, h622, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p624_1, u3ehi4]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h0, h3, h621, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p624_1, u3ehi4]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p624_1, u0ehi1]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h615, h621, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p624_1, u3ehi4]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  rcases p624_3 (m.d 0 2) (by simp) with h638 | h638
                                  · linarith only [h3, h638, hlam]
                                  · linarith only [h610, h638, hlam]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  rcases p624_3 (m.d 0 2) (by simp) with h641 | h641
                                  · linarith only [h3, h641, hlam]
                                  · linarith only [h611, h641, hlam]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h610, hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h615, hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h620, hlam, p624_1]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h0, h615, h621, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p624_1, u3ehi4]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h611, hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h616, hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h621, hlam, p624_1]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [h622, hlam, p624_0]
                                · have p624_0 := h624c.1
                                  have p624_1 := h624c.2.1
                                  have p624_2 := h624c.2.2.1
                                  have p624_3 := h624c.2.2.2
                                  linarith only [hlam, p624_0]
                              · linarith only [h3, h610, h612, h623, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h3, h615, h619, h620, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h3, h621, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h3, h610, h612, h620, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                      · linarith only [h3, h610, h612, h617, h619, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h617, h618, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h613, h615, h617, hlam]
                · linarith only [h3, h611, h616, hc12, hc23, hlam, hphi]
              · linarith only [h3, h610, h615, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
            · linarith only [h3, h663, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h665 | h665
              · rcases m.htr 1 2 5 (by decide) (by decide) with h666 | h666
                · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h668 | h668
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h669 | h669
                      · linarith only [h612, h669, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h671 | h671
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h672 | h672
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h673 | h673
                            · linarith only [h0, h3, h665, h669, h673, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h675 | h675
                              · linarith only [h0, h612, h666, h671, h673, h675, hc02, hlam, hphi, u0ehi3]
                              · rcases h2bigk with h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h3, hc12, hc23, hlam, hphi, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h3, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h3, h671, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p677_1, u3ehi3]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h3, h671, h673, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p677_1, u3ehi3]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h663, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h671, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p677_1, u3ehi3]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h3, h671, h673, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p677_1, u3ehi3]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p677_1, u0ehi1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h665, h671, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p677_1, u3ehi3]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  rcases p677_3 (m.d 0 2) (by simp) with h691 | h691
                                  · linarith only [h3, h691, hlam]
                                  · linarith only [h610, h691, hlam]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  rcases p677_3 (m.d 0 2) (by simp) with h694 | h694
                                  · linarith only [h3, h694, hlam]
                                  · linarith only [h611, h694, hlam]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h610, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h665, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h671, hlam, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h673, hlam, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h611, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h666, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h672, hlam, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h666, h671, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p677_1, u3ehi3]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hlam, p677_0]
                          · linarith only [h3, h672, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h3, h611, h612, h667, h671, hc14, hlam, hphi, ht01, u0ehi3]
                    · linarith only [h667, h668, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h663, h665, h667, hlam]
                · linarith only [h3, h611, h666, hc12, hc23, hlam, hphi]
              · linarith only [h3, h610, h665, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h713 | h713
          · linarith only [h610, h611, h713, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h715 | h715
            · linarith only [h0, h3, h715, hc01, hlam, hphi, u0ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h717 | h717
              · rcases m.htr 1 2 5 (by decide) (by decide) with h718 | h718
                · linarith only [h610, h611, h718, hc12, hlam, hphi, ht01, u0ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h720 | h720
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h721 | h721
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h722 | h722
                      · linarith only [h713, h722, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h724 | h724
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h725 | h725
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h726 | h726
                            · linarith only [h0, h611, h717, h722, h725, h726, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h611, h717, h724, h726, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h1, h721, h725, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h3, h724, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h720, h721, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h715, h717, h720, hlam]
              · linarith only [h3, h610, h717, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h734 | h734
        · rcases m.htr 0 4 5 (by decide) (by decide) with h735 | h735
          · rcases m.htr 1 2 3 (by decide) (by decide) with h736 | h736
            · linarith only [h3, h736, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h738 | h738
              · linarith only [h610, h734, h738, hc12, hlam, hphi, ht01, u0ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h740 | h740
                · rcases m.htr 1 3 4 (by decide) (by decide) with h741 | h741
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h742 | h742
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h743 | h743
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h744 | h744
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h745 | h745
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h746 | h746
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h747 | h747
                              · rcases h2bigk with h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h610, h740, h744, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p748_1, u3ehi4]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h3, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h610, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h610, h744, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p748_1, u3ehi4]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h0, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h736, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h738, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h0, h745, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p748_1, u3ehi4]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p748_1, u0ehi1]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h740, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p748_1, u3ehi4]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h610, h734, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p748_1, u3ehi4]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  rcases p748_3 (m.d 0 2) (by simp) with h763 | h763
                                  · linarith only [h3, h763, hlam]
                                  · linarith only [h734, h763, hlam]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h0, h740, h745, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p748_1, u3ehi4]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h740, h745, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p748_1, u3ehi4]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h744, hlam, p748_1]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  rcases p748_3 (m.d 0 2) (by simp) with h770 | h770
                                  · linarith only [h610, h770, hlam]
                                  · linarith only [h734, h770, hlam]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h734, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h740, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h745, hlam, p748_1]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h746, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hlam, p748_0]
                              · linarith only [h1, h741, h743, h747, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1, h610, h740, h741, h743, h745, h746, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h3, h745, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h1, h3, h734, h741, h744, hc03, hlam, hphi, u0ehi4]
                      · linarith only [h738, h740, h743, hlam]
                    · linarith only [h741, h742, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h784 | h784
                    · linarith only [h741, h784, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h736, h740, h784, hlam]
                · linarith only [h3, h734, h740, hc12, hc23, hlam, hphi]
          · linarith only [h610, h734, h735, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h789 | h789
          · rcases m.htr 1 2 3 (by decide) (by decide) with h790 | h790
            · linarith only [h0, h3, h790, hc01, hlam, hphi, u0ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h792 | h792
              · linarith only [h0, h610, h792, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h794 | h794
                · linarith only [h0, h734, h794, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h796 | h796
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h797 | h797
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h798 | h798
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h800 | h800
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h801 | h801
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h802 | h802
                              · rcases h2bigk with h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h734, h799, h801, hc12, hc23, hlam, hphi, p803_1]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h3, hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h610, hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h734, hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h0, hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h790, hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h792, hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h794, hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p803_1, u0ehi1]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  rcases p803_3 (m.d 0 2) (by simp) with h815 | h815
                                  · linarith only [h3, h815, hlam]
                                  · linarith only [h0, h815, hlam]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h610, hc23, hlam, hphi, ht01, ht12, p803_1, u0ehi1]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h734, hc23, hlam, hphi, ht01, ht12, p803_1, u0ehi1]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p803_1, u0ehi1]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  rcases p803_3 (m.d 0 2) (by simp) with h822 | h822
                                  · linarith only [h610, h822, hlam]
                                  · linarith only [h0, h822, hlam]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h799, hlam, p803_1]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h734, h799, hc23, hlam, hphi, ht01, ht12, p803_1, u0ehi1]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p803_1, u0ehi1]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  rcases p803_3 (m.d 0 2) (by simp) with h829 | h829
                                  · linarith only [h734, h829, hlam]
                                  · linarith only [h0, h829, hlam]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h800, hlam, p803_1]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [h801, hlam, p803_0]
                                · have p803_0 := h803c.1
                                  have p803_1 := h803c.2.1
                                  have p803_2 := h803c.2.2.1
                                  have p803_3 := h803c.2.2.2
                                  linarith only [hlam, p803_0]
                              · linarith only [h1, h796, h798, h802, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h610, h796, h798, h801, hc01, hlam, hphi, u0ehi1]
                          · linarith only [h3, h800, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h1, h3, h796, h799, hc01, hlam, hphi, u0ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h841 | h841
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h842 | h842
                              · linarith only [h796, h798, h842, hlam]
                              · rcases h2bigk with h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h734, hc12, hc25, hlam, hphi, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h3, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h610, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h734, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h790, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h792, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h794, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p844_1, u0ehi1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 2) (by simp) with h856 | h856
                                  · linarith only [h3, h856, hlam]
                                  · linarith only [h0, h856, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h610, hc23, hlam, hphi, ht01, ht12, p844_1, u0ehi3]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h734, hc23, hlam, hphi, ht01, ht12, p844_1, u0ehi1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p844_1, u0ehi1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 2) (by simp) with h863 | h863
                                  · linarith only [h610, h863, hlam]
                                  · linarith only [h0, h863, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h839, hlam, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h734, h839, hc23, hlam, hphi, ht01, ht12, p844_1, u0ehi1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p844_1, u0ehi1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 2) (by simp) with h870 | h870
                                  · linarith only [h734, h870, hlam]
                                  · linarith only [h0, h870, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h840, hlam, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h841, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                            · linarith only [h610, h789, h841, hc04, hlam, hphi, u0ehi1]
                          · linarith only [h3, h840, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h3, h610, h789, h796, h798, h839, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h796, h797, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h880 | h880
                    · linarith only [h796, h880, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h882 | h882
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h883 | h883
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h884 | h884
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h885 | h885
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h886 | h886
                              · rcases h2bigk with h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h3, hc12, hc23, hlam, hphi, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h3, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h610, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h734, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h0, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h790, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h792, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h794, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p887_1, u0ehi1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  rcases p887_3 (m.d 0 2) (by simp) with h899 | h899
                                  · linarith only [h3, h899, hlam]
                                  · linarith only [h0, h899, hlam]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h610, hc23, hlam, hphi, ht01, ht12, p887_1, u0ehi3]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h734, hc23, hlam, hphi, ht01, ht12, p887_1, u0ehi1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p887_1, u0ehi1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  rcases p887_3 (m.d 0 2) (by simp) with h906 | h906
                                  · linarith only [h610, h906, hlam]
                                  · linarith only [h0, h906, hlam]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h883, hlam, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h734, h883, hc23, hlam, hphi, ht01, ht12, p887_1, u0ehi1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p887_1, u0ehi1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  rcases p887_3 (m.d 0 2) (by simp) with h913 | h913
                                  · linarith only [h734, h913, hlam]
                                  · linarith only [h0, h913, hlam]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h884, hlam, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h885, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hlam, p887_0]
                              · linarith only [h610, h789, h796, h883, h886, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h610, h796, h882, h883, h885, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                          · linarith only [h883, h884, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h3, h883, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h923 | h923
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h924 | h924
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h925 | h925
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h926 | h926
                              · linarith only [h796, h882, h926, hc34, hlam, hphi, u3ehi1]
                              · linarith only [h610, h789, h796, h923, h926, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h610, h789, h925, hlam]
                          · linarith only [h3, h924, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h3, h923, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h932 | h932
            · linarith only [h3, h932, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h934 | h934
              · linarith only [h0, h610, h934, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h936 | h936
                · linarith only [h0, h734, h936, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h938 | h938
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h939 | h939
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h940 | h940
                      · linarith only [h789, h940, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h942 | h942
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h943 | h943
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h944 | h944
                            · linarith only [h610, h789, h942, h944, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h610, h944, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                          · linarith only [h1, h939, h943, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h1, h3, h939, h942, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h938, h939, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h950 | h950
                    · linarith only [h938, h950, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h952 | h952
                      · linarith only [h610, h789, h952, hc14, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h954 | h954
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h955 | h955
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h956 | h956
                            · linarith only [h610, h789, h954, h956, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h610, h956, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                          · linarith only [h3, h955, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h3, h954, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h961 | h961
    · rcases m.htr 0 2 4 (by decide) (by decide) with h962 | h962
      · rcases m.htr 0 2 5 (by decide) (by decide) with h963 | h963
        · linarith only [h0, h2, h963, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h965 | h965
          · linarith only [h0, h2, h962, h965, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h967 | h967
            · linarith only [h0, h2, h967, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h961, h963, h967, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h970 | h970
        · linarith only [h0, h2, h970, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h972 | h972
          · rcases m.htr 1 2 3 (by decide) (by decide) with h973 | h973
            · linarith only [h0, h2, h973, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h961, h962, h973, hc12, hc24, hlam, hphi]
          · linarith only [h961, h962, h972, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h977 | h977
      · rcases m.htr 0 2 5 (by decide) (by decide) with h978 | h978
        · linarith only [h0, h2, h978, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h980 | h980
          · linarith only [h1, h2, h961, h977, h980, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h982 | h982
            · linarith only [h961, h982, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h984 | h984
              · rcases m.htr 1 2 5 (by decide) (by decide) with h985 | h985
                · linarith only [h1, h977, h978, h982, h985, hc01, hlam, hphi, u0ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h987 | h987
                  · linarith only [h1, h2, h985, h987, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h982, h984, h987, hlam]
              · linarith only [h961, h977, h984, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h991 | h991
        · linarith only [h0, h2, h991, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h993 | h993
          · rcases m.htr 1 2 3 (by decide) (by decide) with h994 | h994
            · linarith only [h961, h994, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h996 | h996
              · linarith only [h1, h977, h994, h996, hc01, hlam, hphi, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h998 | h998
                · linarith only [h1, h2, h991, h994, h998, hc15, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1000 | h1000
                  · linarith only [h1, h1000, h2, h998, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1002 | h1002
                    · linarith only [h1, h1002, h2, h998, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h1, h1002, h2, hc35, hlam, hphi, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1005 | h1005
            · linarith only [h1005, h961, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1007 | h1007
              · linarith only [h1, h1005, h1007, h977, hc01, hlam, hphi, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1009 | h1009
                · linarith only [h1, h1005, h1009, h2, h991, hc15, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1011 | h1011
                  · linarith only [h1, h1009, h1011, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1013 | h1013
                    · linarith only [h1, h1009, h1013, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h1, h1013, h2, hc35, hlam, hphi, u3ehi1]

end R2N4
