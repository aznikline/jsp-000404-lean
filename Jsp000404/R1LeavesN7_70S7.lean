import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h11, h14, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h17, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h11, h17, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h11, h12, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h0, h11, h21, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                              · linarith only [h0, h11, h24, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                                · linarith only [h21, h26, h9, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                                  · linarith only [h0, h10, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h11, h23, h28, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                              · linarith only [h0, h11, h23, h31, h4, h7, h8, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                                · linarith only [h0, h33, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                                  · linarith only [h10, h23, h35, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                                    · linarith only [h11, h23, h37, hc34, hlam, hphi, u3ehi1]
                                    · linarith only [h0, h11, h37, h4, h7, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h10, h5, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                      · linarith only [h41, h9, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                                    · linarith only [h1, h43, h49, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h2, h45, h49, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h41, h45, h48, hlam]
                                · linarith only [h44, h47, h9, hlam]
                              · linarith only [h44, h46, h9, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                                  · linarith only [h41, h45, h55, h57, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h4, h41, h57, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h1, h44, h56, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h4, h43, h45, h55, h7, h8, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h43, h44, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                          · linarith only [h0, h4, h43, h63, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                              · linarith only [h0, h4, h43, h66, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · linarith only [h66, h9, hc34, hlam, hphi, ht23, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                              · linarith only [h43, h69, h9, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h4, h69, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h74 | h74
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h75 | h75
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                            · linarith only [h2, h76, h8, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                              · linarith only [h0, h72, h78, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1, h74, h78, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h74, h75, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h7, h74, h8, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h5, h73, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
                      · linarith only [h72, h84, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h5, h8, h84, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h87 | h87
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                        · linarith only [h1, h7, h90, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                          · linarith only [h1, h7, h92, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                              · linarith only [h0, h4, h7, h95, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                                · linarith only [h88, h92, h97, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
                                  · linarith only [h0, h89, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h2, h94, h99, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h7, h87, h89, h94, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h5, h88, h89, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h4, h7, h88, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                        · linarith only [h1, h107, h7, h87, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
                          · linarith only [h1, h109, h7, h87, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                            · linarith only [h111, h2, h7, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                              · linarith only [h1, h105, h113, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                                · linarith only [h1, h105, h115, h7, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                                  · linarith only [h0, h106, h117, h87, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                                    · linarith only [h119, h7, h87, hc34, hlam, hphi, u3ehi0]
                                    · linarith only [h1, h105, h119, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h106, h5, h87, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                    · linarith only [h105, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
              · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h126 | h126
            · linarith only [h126, h4, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h128 | h128
              · linarith only [h128, h4, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
                · rcases m.htr 0 4 5 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
                    · linarith only [h0, h132, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h134 | h134
                      · linarith only [h0, h126, h134, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h139 | h139
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h142 | h142
                                    · linarith only [h1, h136, h142, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h138, h142, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h126, h138, h141, h2, hlam]
                                · linarith only [h0, h140, h4, hc35, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h1, h137, h139, h4, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h130, h131, h134, h138, h4, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h136, h137, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h130, h132, h136, h4, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                    · linarith only [h0, h151, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h153 | h153
                      · linarith only [h0, h126, h131, h153, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h157 | h157
                            · linarith only [h126, h131, h157, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h161 | h161
                                  · linarith only [h0, h126, h131, h161, hc24, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h126, h161, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h1, h156, h160, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h1, h156, h159, h4, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h155, h156, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h130, h131, h155, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                    · linarith only [h0, h126, h169, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                      · linarith only [h0, h130, h171, h4, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                        · linarith only [h1, h130, h173, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h175 | h175
                          · linarith only [h1, h130, h175, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                              · linarith only [h0, h130, h178, h4, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h178, h4, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h130, h168, h171, h177, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h182 | h182
                    · linarith only [h0, h182, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h184 | h184
                      · linarith only [h0, h184, h4, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
                        · linarith only [h1, h130, h168, h186, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h188 | h188
                          · linarith only [h1, h130, h168, h188, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h190 | h190
                            · linarith only [h130, h168, h190, h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h192 | h192
                              · linarith only [h0, h130, h192, h4, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h192, h4, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h195 | h195
          · rcases m.htr 0 2 4 (by decide) (by decide) with h196 | h196
            · rcases m.htr 0 2 5 (by decide) (by decide) with h197 | h197
              · linarith only [h0, h197, h3, hlam]
              · linarith only [h196, h197, hc25, hlam, hphi, u2ehi3]
            · linarith only [h195, h196, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h201 | h201
            · linarith only [h195, h201, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h203 | h203
              · linarith only [h195, h203, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h205 | h205
                · rcases m.htr 0 4 5 (by decide) (by decide) with h206 | h206
                  · linarith only [h1, h205, h206, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
                    · linarith only [h0, h201, h206, h208, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
                      · linarith only [h1, h201, h208, h210, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h212 | h212
                        · linarith only [h1, h212, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h205, h212, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
                  · linarith only [h2, h215, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                    · linarith only [h0, h195, h217, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                      · linarith only [h0, h201, h219, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                        · linarith only [h1, h221, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
                          · linarith only [h2, h221, h223, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h2, h221, h223, h3, hc35, hlam, hphi, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h226 | h226
        · rcases m.htr 0 2 3 (by decide) (by decide) with h227 | h227
          · rcases m.htr 0 2 4 (by decide) (by decide) with h228 | h228
            · linarith only [h0, h2, h228, hlam]
            · linarith only [h227, h228, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h231 | h231
            · linarith only [h227, h231, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h233 | h233
              · linarith only [h227, h233, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h235 | h235
                · linarith only [h1, h2, h235, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
                    · linarith only [h0, h2, h227, h238, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                      · linarith only [h0, h227, h240, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h1, h2, h238, h240, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h237, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h244 | h244
          · rcases m.htr 0 2 4 (by decide) (by decide) with h245 | h245
            · linarith only [h0, h2, h245, hlam]
            · linarith only [h244, h245, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h248 | h248
            · linarith only [h244, h248, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h250 | h250
              · linarith only [h244, h250, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h252 | h252
                · linarith only [h1, h2, h252, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h254 | h254
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
                    · linarith only [h0, h2, h255, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h257 | h257
                      · linarith only [h1, h226, h248, h254, h255, h257, hlam]
                      · linarith only [h1, h2, h255, h257, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h1, h2, h254, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h261 | h261
      · rcases m.htr 0 1 5 (by decide) (by decide) with h262 | h262
        · rcases m.htr 0 2 3 (by decide) (by decide) with h263 | h263
          · linarith only [h0, h1, h263, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h265 | h265
            · linarith only [h263, h265, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h267 | h267
              · linarith only [h263, h267, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h269 | h269
                · rcases m.htr 0 4 5 (by decide) (by decide) with h270 | h270
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
                    · linarith only [h0, h263, h271, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h271, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
                    · linarith only [h0, h1, h263, h274, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h0, h1, h274, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h269, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h278 | h278
          · linarith only [h0, h1, h278, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h280 | h280
            · linarith only [h278, h280, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h282 | h282
              · linarith only [h278, h282, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h284 | h284
                · rcases m.htr 0 4 5 (by decide) (by decide) with h285 | h285
                  · linarith only [h261, h262, h285, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                    · linarith only [h0, h278, h287, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h287, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h284, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h291 | h291
        · rcases m.htr 0 2 3 (by decide) (by decide) with h292 | h292
          · linarith only [h0, h1, h292, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h294 | h294
            · linarith only [h292, h294, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h296 | h296
              · linarith only [h292, h296, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h298 | h298
                · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
                    · linarith only [h0, h1, h292, h300, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h300, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h261, h299, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h298, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h305 | h305
          · linarith only [h0, h1, h305, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h307 | h307
            · linarith only [h305, h307, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h309 | h309
              · linarith only [h305, h309, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h311 | h311
                · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
                    · linarith only [h0, h1, h305, h313, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h313, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h261, h312, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h311, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h318 | h318
    · rcases m.htr 0 1 4 (by decide) (by decide) with h319 | h319
      · rcases m.htr 0 1 5 (by decide) (by decide) with h320 | h320
        · rcases m.htr 0 2 3 (by decide) (by decide) with h321 | h321
          · rcases m.htr 0 2 4 (by decide) (by decide) with h322 | h322
            · rcases m.htr 0 2 5 (by decide) (by decide) with h323 | h323
              · rcases m.htr 0 3 4 (by decide) (by decide) with h324 | h324
                · rcases m.htr 0 4 5 (by decide) (by decide) with h325 | h325
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h327 | h327
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h328 | h328
                        · linarith only [h0, h318, h328, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h318, h324, h328, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h320, h327, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h318, h326, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h333 | h333
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h335 | h335
                        · linarith only [h0, h318, h335, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h318, h324, h333, h335, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h320, h334, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h318, h333, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h340 | h340
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h343 | h343
                        · linarith only [h318, h324, h343, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h345 | h345
                          · linarith only [h0, h319, h343, h345, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
                            · linarith only [h0, h319, h347, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h0, h319, h340, h341, h343, h347, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h318, h341, h342, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h318, h341, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h353 | h353
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h354 | h354
                        · linarith only [h0, h318, h354, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h356 | h356
                          · linarith only [h0, h319, h354, h356, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h358 | h358
                            · linarith only [h0, h319, h324, h340, h358, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h360 | h360
                              · linarith only [h318, h324, h352, h360, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h362 | h362
                                · linarith only [h352, h356, h362, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h364 | h364
                                  · linarith only [h319, h340, h353, h364, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h366 | h366
                                    · linarith only [h318, h324, h340, h352, h366, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h318, h324, h352, h366, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h318, h352, h353, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h318, h352, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h321, h323, hc25, hlam, hphi, u2ehi2]
            · linarith only [h321, h322, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h318, h321, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h374 | h374
          · rcases m.htr 0 2 4 (by decide) (by decide) with h375 | h375
            · rcases m.htr 0 2 5 (by decide) (by decide) with h376 | h376
              · rcases m.htr 0 3 4 (by decide) (by decide) with h377 | h377
                · rcases m.htr 0 4 5 (by decide) (by decide) with h378 | h378
                  · linarith only [h319, h320, h378, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h380 | h380
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h381 | h381
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h382 | h382
                        · linarith only [h0, h318, h382, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h318, h377, h382, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h318, h377, h381, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h318, h377, h380, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h387 | h387
                  · linarith only [h319, h320, h387, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h391 | h391
                        · linarith only [h318, h377, h391, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h393 | h393
                          · linarith only [h0, h319, h391, h393, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h319, h320, h389, h391, h393, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h318, h389, h390, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h318, h389, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h375, h376, hc25, hlam, hphi, u2ehi3]
            · linarith only [h374, h375, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h318, h374, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h401 | h401
        · rcases m.htr 0 2 3 (by decide) (by decide) with h402 | h402
          · rcases m.htr 0 2 4 (by decide) (by decide) with h403 | h403
            · rcases m.htr 0 2 5 (by decide) (by decide) with h404 | h404
              · rcases m.htr 0 3 4 (by decide) (by decide) with h405 | h405
                · linarith only [h318, h319, h405, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h407 | h407
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h409 | h409
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h410 | h410
                        · linarith only [h318, h319, h405, h409, h410, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h318, h319, h408, h410, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h403, h409, hlam]
                    · linarith only [h0, h403, h408, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h318, h319, h407, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h402, h404, hc25, hlam, hphi, u2ehi2]
            · linarith only [h402, h403, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h318, h402, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h419 | h419
          · rcases m.htr 0 2 4 (by decide) (by decide) with h420 | h420
            · rcases m.htr 0 2 5 (by decide) (by decide) with h421 | h421
              · rcases m.htr 0 3 4 (by decide) (by decide) with h422 | h422
                · linarith only [h318, h319, h422, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h424 | h424
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h426 | h426
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                        · linarith only [h318, h319, h422, h426, h427, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h318, h319, h425, h427, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h318, h420, h425, h426, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h420, h425, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h318, h319, h424, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h420, h421, hc25, hlam, hphi, u2ehi3]
            · linarith only [h419, h420, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h318, h419, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h436 | h436
      · rcases m.htr 0 1 5 (by decide) (by decide) with h437 | h437
        · rcases m.htr 0 2 3 (by decide) (by decide) with h438 | h438
          · rcases m.htr 0 2 4 (by decide) (by decide) with h439 | h439
            · rcases m.htr 0 2 5 (by decide) (by decide) with h440 | h440
              · rcases m.htr 0 3 4 (by decide) (by decide) with h441 | h441
                · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h444 | h444
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h445 | h445
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h446 | h446
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h447 | h447
                            · linarith only [h318, h436, h443, h447, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h318, h436, h442, h443, h444, h447, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h318, h437, h446, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h318, h436, h438, h441, h444, h445, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h438, h444, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h436, h438, h442, h443, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h454 | h454
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h455 | h455
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h456 | h456
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h457 | h457
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h458 | h458
                            · linarith only [h0, h436, h442, h458, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h460 | h460
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h461 | h461
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h462 | h462
                                  · linarith only [h436, h442, h455, h462, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h464 | h464
                                    · linarith only [h436, h442, h455, h460, h464, hlam]
                                    · rcases h0bigk with h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [hlam, p466_0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h0, hlam, p466_1]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h318, hlam, p466_0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h318, h454, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p466_1]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h318, h454, hc12, hlam, hphi, ht01, ht0b, ht5b, p466_1, u5ehi0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p466_1]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [hlam, p466_0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p466_1, u3ehi0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h0, h436, h455, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p466_1, u2ehi3]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h0, h437, hc12, hlam, hphi, ht01, ht0b, ht5b, p466_1, u5ehi1]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h436, h455, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p466_1, u2ehi3]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h438, hlam, p466_1]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [hlam, p466_0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h318, h436, h454, h455, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p466_1, u2ehi3]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h318, h436, h442, h454, h455, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p466_1, u2ehi3]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h436, hlam, p466_0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h439, hlam, p466_0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h441, hlam, p466_0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [hlam, p466_0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h442, hlam, p466_0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h437, hlam, p466_0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h440, hlam, p466_1]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p466_1, u3ehi0]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [h436, h455, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p466_1, u2ehi3]
                                      · have p466_0 := h466c.1
                                        have p466_1 := h466c.2.1
                                        have p466_2 := h466c.2.2.1
                                        have p466_3 := h466c.2.2.2
                                        linarith only [hlam, p466_0]
                                · linarith only [h0, h437, h457, h461, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h441, h442, h460, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h318, h437, h457, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h318, h436, h455, h456, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h318, h437, h454, h455, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h437, h454, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h318, h436, h441, hlam]
              · linarith only [h438, h440, hc25, hlam, hphi, u2ehi2]
            · linarith only [h438, h439, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h501 | h501
            · linarith only [h438, h501, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h436, h501, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h504 | h504
          · rcases m.htr 0 2 4 (by decide) (by decide) with h505 | h505
            · rcases m.htr 0 2 5 (by decide) (by decide) with h506 | h506
              · rcases m.htr 0 3 4 (by decide) (by decide) with h507 | h507
                · rcases m.htr 0 4 5 (by decide) (by decide) with h508 | h508
                  · linarith only [h436, h437, h508, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h510 | h510
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h511 | h511
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h512 | h512
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h513 | h513
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h514 | h514
                            · linarith only [h436, h437, h508, h510, h513, h514, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h436, h437, h511, h514, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                          · linarith only [h318, h436, h511, h513, hc35, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h318, h436, h511, h512, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h504, h511, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h504, h510, hlam]
                · linarith only [h318, h436, h507, hlam]
              · linarith only [h504, h506, hc25, hlam, hphi, u2ehi2]
            · linarith only [h504, h505, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h524 | h524
            · linarith only [h504, h524, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h436, h524, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h527 | h527
        · rcases m.htr 0 2 3 (by decide) (by decide) with h528 | h528
          · rcases m.htr 0 2 4 (by decide) (by decide) with h529 | h529
            · rcases m.htr 0 2 5 (by decide) (by decide) with h530 | h530
              · rcases m.htr 0 3 4 (by decide) (by decide) with h531 | h531
                · rcases m.htr 0 4 5 (by decide) (by decide) with h532 | h532
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h534 | h534
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h535 | h535
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h537 | h537
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h538 | h538
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h539 | h539
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h540 | h540
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h541 | h541
                                    · linarith only [h528, h538, h541, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h436, h527, h533, h535, h537, h541, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h436, h527, h533, h535, h537, h540, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h436, h527, h533, h535, h536, h539, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h546 | h546
                                · linarith only [h538, h546, hc34, hlam, hphi, u3ehi4]
                                · linarith only [h436, h527, h533, h535, h536, h546, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h436, h527, h537, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                          · linarith only [h318, h531, h536, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h318, h531, h535, hlam]
                      · linarith only [h318, h527, h533, h534, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h529, h533, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h436, h527, h532, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h555 | h555
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h556 | h556
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h557 | h557
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h558 | h558
                        · linarith only [h318, h527, h531, h556, h558, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                        · linarith only [h318, h527, h558, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h0, h527, h557, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h527, h528, h556, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                  · linarith only [h436, h527, h555, hlam]
              · linarith only [h528, h530, hc25, hlam, hphi, u2ehi2]
            · linarith only [h528, h529, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h566 | h566
            · linarith only [h528, h566, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h568 | h568
              · linarith only [h528, h568, hc23, hlam, hphi, u2ehi4]
              · linarith only [h0, h527, h568, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h571 | h571
          · rcases m.htr 0 2 4 (by decide) (by decide) with h572 | h572
            · rcases m.htr 0 2 5 (by decide) (by decide) with h573 | h573
              · rcases m.htr 0 3 4 (by decide) (by decide) with h574 | h574
                · rcases m.htr 0 4 5 (by decide) (by decide) with h575 | h575
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h576 | h576
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h577 | h577
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h578 | h578
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h579 | h579
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h580 | h580
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h581 | h581
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h582 | h582
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h583 | h583
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h584 | h584
                                    · linarith only [h0, h571, h581, h584, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                    · linarith only [h0, h571, h581, h583, h584, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h587 | h587
                                    · linarith only [h583, h587, hc34, hlam, hphi, ht23, u2ehi3]
                                    · rcases h0bigk with h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [hlam, p589_0]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h0, hlam, p589_1]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h318, hlam, p589_0]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h436, hlam, p589_1]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h527, hlam, p589_1]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p589_1]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [hlam, p589_0]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p589_1, u3ehi0]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h0, h575, h583, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p589_1, u2ehi3]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p589_1, u5ehi0]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h318, h576, hc01, hc12, hlam, hphi, p589_1]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h571, hlam, p589_1]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [hlam, p589_0]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h318, h575, h576, h583, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p589_1, u2ehi3]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h318, h575, h576, h583, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p589_1, u2ehi3]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h436, h576, h578, hc01, hc12, hlam, hphi, p589_1]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h572, hlam, p589_0]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h574, hlam, p589_0]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [hlam, p589_0]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h436, h575, h576, h578, h583, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p589_1, u2ehi3]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h527, h576, h578, h580, hc01, hc12, hlam, hphi, p589_1]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h573, hlam, p589_1]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h527, h576, h578, h580, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p589_1, u3ehi0]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [h575, hlam, p589_1]
                                      · have p589_0 := h589c.1
                                        have p589_1 := h589c.2.1
                                        have p589_2 := h589c.2.2.1
                                        have p589_3 := h589c.2.2.2
                                        linarith only [hlam, p589_0]
                                · linarith only [h576, h579, h581, h582, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h616 | h616
                                · linarith only [h581, h616, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h618 | h618
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h619 | h619
                                    · rcases h0bigk with h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, hlam, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h318, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h436, hlam, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h527, hlam, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, h574, h616, h619, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p620_1, u2ehi2]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, h436, hc01, hc12, hlam, hphi, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p620_1, u5ehi0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h318, h576, hc01, hc12, hlam, hphi, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h571, hlam, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h318, h572, h576, h618, hc12, hlam, hphi, ht01, ht0b, ht5b, p620_1, u5ehi4]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h318, h576, hc12, hlam, hphi, ht01, ht0b, ht5b, p620_1, u5ehi0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h436, h576, h578, hc01, hc12, hlam, hphi, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h572, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h574, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h436, h573, h576, h578, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p620_1, u2ehi4]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h527, h576, h578, h580, hc01, hc12, hlam, hphi, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h573, hlam, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h527, h576, h578, h580, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p620_1, u3ehi0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h575, hlam, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [hlam, p620_0]
                                    · linarith only [h0, h572, h618, h619, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h647 | h647
                                    · linarith only [h318, h574, h576, h618, h647, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · linarith only [h436, h575, h576, h578, h581, h647, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h436, h575, h580, hlam]
                          · linarith only [h318, h574, h579, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h318, h574, h578, hlam]
                      · linarith only [h0, h572, h577, hlam]
                    · linarith only [h0, h571, h576, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h655 | h655
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h656 | h656
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h657 | h657
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h658 | h658
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h659 | h659
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h660 | h660
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h661 | h661
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h662 | h662
                                  · linarith only [h572, h575, h662, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h664 | h664
                                    · linarith only [h571, h572, h575, h660, h664, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h0bigk with h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [hlam, p666_0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h0, hlam, p666_1]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h318, hlam, p666_0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h436, hlam, p666_1]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h527, hlam, p666_1]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p666_1]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [hlam, p666_0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p666_1, u3ehi0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h0, h572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p666_1, u2ehi3]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p666_1, u5ehi0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h318, hc01, hc13, hlam, hphi, p666_1]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h571, hlam, p666_1]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [hlam, p666_0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h0, h571, h572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p666_1, u2ehi3]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h0, h571, h572, h575, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p666_1, u2ehi3]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h575, h659, hc01, hc14, hlam, hphi, p666_1]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h572, hlam, p666_0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h574, hlam, p666_0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [hlam, p666_0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h575, hlam, p666_0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h527, h659, hc01, hc14, hlam, hphi, p666_1]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h573, hlam, p666_1]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h575, h655, h657, h659, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p666_1, u3ehi0]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [h575, h655, h657, h659, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p666_1]
                                      · have p666_0 := h666c.1
                                        have p666_1 := h666c.2.1
                                        have p666_2 := h666c.2.2.1
                                        have p666_3 := h666c.2.2.2
                                        linarith only [hlam, p666_0]
                                · linarith only [h655, h658, h660, h661, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h574, h575, h655, h657, h659, h660, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h694 | h694
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h695 | h695
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h696 | h696
                                  · linarith only [h436, h659, h696, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h698 | h698
                                    · linarith only [h436, h572, h659, h694, h698, hlam]
                                    · rcases h0bigk with h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [hlam, p700_0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h0, hlam, p700_1]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h318, hlam, p700_0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h436, hlam, p700_1]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h527, hlam, p700_1]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p700_1]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [hlam, p700_0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p700_1, u3ehi0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h0, h572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p700_1, u2ehi3]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p700_1, u5ehi0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h318, h655, hc01, hc12, hlam, hphi, p700_1]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h571, hlam, p700_1]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [hlam, p700_0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h318, h572, h655, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p700_1, u2ehi3]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h318, h572, h575, h655, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p700_1, u2ehi3]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h436, hc01, hc14, hlam, hphi, p700_1]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h572, hlam, p700_0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h574, hlam, p700_0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [hlam, p700_0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h575, hlam, p700_0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h527, hc01, hc15, hlam, hphi, p700_1]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h573, hlam, p700_1]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h527, h659, hc45, hlam, hphi, ht34, p700_1, u3ehi0]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [h527, h659, hc04, hc45, hlam, hphi, p700_1]
                                      · have p700_0 := h700c.1
                                        have p700_1 := h700c.2.1
                                        have p700_2 := h700c.2.2.1
                                        have p700_3 := h700c.2.2.2
                                        linarith only [hlam, p700_0]
                                · linarith only [h655, h658, h694, h695, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h436, h574, h659, h694, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h318, h574, h658, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h318, h574, h657, hlam]
                      · linarith only [h0, h571, h656, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h571, h655, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h732 | h732
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h733 | h733
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h734 | h734
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h735 | h735
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h736 | h736
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h737 | h737
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h738 | h738
                              · linarith only [h571, h574, h738, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h740 | h740
                                · linarith only [h571, h574, h733, h735, h740, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h742 | h742
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h743 | h743
                                    · rcases h0bigk with h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h0, hlam, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h318, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h436, hlam, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h527, hlam, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h0, h571, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p744_1, u2ehi2]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h0, h572, h742, hc12, hlam, hphi, ht01, ht0b, ht5b, p744_1, u5ehi4]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p744_1, u5ehi0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h318, h733, hc01, hc12, hlam, hphi, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h571, hlam, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h574, hlam, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h573, h574, h733, h735, h740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p744_1, u2ehi2]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h436, hc01, hc14, hlam, hphi, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h572, hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h574, h733, h735, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p744_1, u3ehi0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [hlam, p744_0]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h573, h574, h733, h735, h740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p744_1, u2ehi2]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h527, h737, hc01, hc14, hlam, hphi, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h573, hlam, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h571, h574, h732, h733, h735, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p744_1, u2ehi2]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [h732, hlam, p744_1]
                                      · have p744_0 := h744c.1
                                        have p744_1 := h744c.2.1
                                        have p744_2 := h744c.2.2.1
                                        have p744_3 := h744c.2.2.2
                                        linarith only [hlam, p744_0]
                                    · linarith only [h572, h574, h732, h742, h743, hc02, hlam, hphi, ht0b, ht5b, u5ehi0]
                                  · linarith only [h574, h732, h733, h735, h742, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h436, h574, h732, h733, h735, h737, hc01, hc12, hlam, hphi]
                          · linarith only [h574, h735, h736, hc35, hlam, hphi, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h774 | h774
                          · linarith only [h735, h774, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h776 | h776
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h777 | h777
                              · linarith only [h0, h571, h735, h777, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h779 | h779
                                · linarith only [h318, h774, h779, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h781 | h781
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h782 | h782
                                    · rcases h0bigk with h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [hlam, p783_0]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h0, hlam, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h318, hlam, p783_0]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h436, hlam, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h527, hlam, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [hlam, p783_0]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h0, h571, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p783_1, u2ehi2]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h0, h572, h781, hc12, hlam, hphi, ht01, ht0b, ht5b, p783_1, u5ehi4]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p783_1, u5ehi0]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h318, hc01, hc13, hlam, hphi, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h571, hlam, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [hlam, p783_0]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h574, hlam, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h318, h573, h774, h779, h782, hc34, hlam, hphi, ht23, p783_1, u2ehi2]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h436, hc01, hc14, hlam, hphi, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h572, hlam, p783_0]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h574, hc34, hlam, hphi, p783_1, u3ehi0]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [hlam, p783_0]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h573, h574, h779, hc34, hlam, hphi, ht23, p783_1, u2ehi2]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h527, hc01, hc15, hlam, hphi, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h573, hlam, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h436, h571, h732, h735, hc34, hlam, hphi, ht23, p783_1, u2ehi2]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [h732, hlam, p783_1]
                                      · have p783_0 := h783c.1
                                        have p783_1 := h783c.2.1
                                        have p783_2 := h783c.2.2.1
                                        have p783_3 := h783c.2.2.2
                                        linarith only [hlam, p783_0]
                                    · linarith only [h436, h735, h781, h782, hc01, hc24, hlam, hphi, ht12]
                                  · linarith only [h574, h732, h781, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h436, h732, h776, hlam]
                      · linarith only [h0, h571, h734, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h571, h733, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h814 | h814
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h815 | h815
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h816 | h816
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h817 | h817
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h818 | h818
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h819 | h819
                              · linarith only [h571, h574, h819, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h821 | h821
                                · linarith only [h571, h574, h732, h814, h816, h818, h821, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h823 | h823
                                  · linarith only [h571, h572, h574, h732, h823, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h825 | h825
                                    · linarith only [h571, h574, h732, h825, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h571, h574, h818, h825, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h571, h574, h816, h818, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h571, h574, h816, h817, hc35, hlam, hphi, ht23, u2ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h830 | h830
                          · linarith only [h816, h830, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h832 | h832
                            · linarith only [h571, h574, h732, h816, h832, hc34, hlam, hphi, ht23, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h834 | h834
                              · linarith only [h318, h571, h816, h832, h834, hc45, hlam, hphi, ht34, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h836 | h836
                                · linarith only [h318, h571, h816, h832, h836, hc45, hlam, hphi, ht34, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h838 | h838
                                  · linarith only [h436, h572, h832, h838, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h840 | h840
                                    · linarith only [h318, h816, h832, h840, hc34, hlam, hphi, u3ehi0]
                                    · linarith only [h571, h574, h840, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h571, h815, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h571, h814, hlam]
              · linarith only [h571, h573, hc25, hlam, hphi, u2ehi2]
            · linarith only [h571, h572, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h847 | h847
            · linarith only [h571, h847, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h849 | h849
              · linarith only [h571, h849, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h851 | h851
                · rcases m.htr 0 4 5 (by decide) (by decide) with h852 | h852
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h853 | h853
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h854 | h854
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h855 | h855
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h856 | h856
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h857 | h857
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h858 | h858
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h859 | h859
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h860 | h860
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h861 | h861
                                    · linarith only [h571, h851, h853, h861, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                    · linarith only [h847, h852, h853, h858, h861, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h847, h852, h860, hlam]
                                · linarith only [h571, h859, hc35, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h571, h858, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h436, h852, h857, hlam]
                          · linarith only [h847, h854, h855, h856, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h318, h851, h855, hlam]
                      · linarith only [h853, h854, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h871 | h871
                      · linarith only [h853, h871, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h873 | h873
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h874 | h874
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h875 | h875
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h876 | h876
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h877 | h877
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h878 | h878
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h879 | h879
                                    · rcases h0bigk with h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h0, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h318, hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h436, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h527, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h849, hc01, hc25, hlam, hphi, ht12, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h571, hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h847, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h849, hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h318, hc01, hc13, hlam, hphi, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h571, hc23, hlam, hphi, p880_1, u2ehi0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h571, h851, h879, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p880_1, u5ehi4]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h318, h853, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p880_1, u5ehi0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h436, hc01, hc14, hlam, hphi, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h847, h876, hc23, hlam, hphi, p880_1, u2ehi0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h851, hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h318, h849, h851, h853, hc23, hlam, hphi, p880_1, u2ehi0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h527, hc01, hc15, hlam, hphi, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h849, h876, h878, hc23, hlam, hphi, p880_1, u2ehi0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h851, h852, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h852, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [hlam, p880_0]
                                    · rcases h0bigk with h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [hlam, p906_0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h0, hlam, p906_1]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h318, hlam, p906_0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h436, hlam, p906_1]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h527, hlam, p906_1]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h0, h871, h876, hc01, hc23, hlam, hphi, ht12, p906_1]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [hlam, p906_0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h571, hlam, p906_0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h847, hlam, p906_1]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h849, hlam, p906_0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h318, h853, hc01, hc23, hlam, hphi, ht12, p906_1]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h318, h853, hc23, hlam, hphi, p906_1, u2ehi0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [hlam, p906_0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h318, h852, h853, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p906_1, u5ehi0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h318, h852, h853, h879, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p906_1, u3ehi3]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h436, h871, h876, hc01, hc23, hlam, hphi, ht12, p906_1]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h436, h871, h876, hc23, hlam, hphi, p906_1, u2ehi0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h851, hlam, p906_0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [hlam, p906_0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h436, h852, h871, h876, h879, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p906_1, u3ehi3]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h527, h871, h875, h876, hc01, hc23, hlam, hphi, ht12, p906_1]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h527, h871, h875, h876, hc23, hlam, hphi, p906_1, u2ehi0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h527, h871, h875, h876, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p906_1, u3ehi0]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [h852, hlam, p906_1]
                                      · have p906_0 := h906c.1
                                        have p906_1 := h906c.2.1
                                        have p906_2 := h906c.2.2.1
                                        have p906_3 := h906c.2.2.2
                                        linarith only [hlam, p906_0]
                                  · linarith only [h871, h878, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h0, h871, h876, h877, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h851, h853, h874, h876, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h318, h436, h851, h852, h875, hc01, hc13, hlam, hphi]
                          · linarith only [h318, h851, h874, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h318, h851, h873, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h938 | h938
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h939 | h939
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h940 | h940
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h941 | h941
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h942 | h942
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h943 | h943
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h944 | h944
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h945 | h945
                                  · linarith only [h847, h852, h945, hc24, hlam, hphi, u2ehi0]
                                  · linarith only [h847, h938, h940, h942, h945, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                · linarith only [h571, h944, hc35, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h571, h851, h943, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · linarith only [h847, h939, h942, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h318, h851, h941, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h571, h851, h938, h940, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h938, h939, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h954 | h954
                      · linarith only [h938, h954, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h956 | h956
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h957 | h957
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h958 | h958
                            · linarith only [h847, h852, h954, h958, hc24, hlam, hphi, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h960 | h960
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h961 | h961
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h962 | h962
                                  · linarith only [h954, h958, h960, h962, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h847, h962, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h571, h957, h961, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · linarith only [h851, h938, h957, h960, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h318, h851, h957, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h318, h851, h956, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h969 | h969
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h970 | h970
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h971 | h971
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h972 | h972
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h973 | h973
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h974 | h974
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h975 | h975
                              · linarith only [h571, h851, h970, h975, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · linarith only [h571, h975, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h436, h969, h974, hlam]
                          · linarith only [h571, h851, h972, h973, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h571, h970, h972, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h571, h970, h971, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h982 | h982
                      · linarith only [h970, h982, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h984 | h984
                        · linarith only [h571, h851, h970, h984, hc23, hlam, hphi, u2ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h986 | h986
                          · linarith only [h984, h986, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h988 | h988
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h989 | h989
                              · linarith only [h0, h970, h984, h989, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h571, h989, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h436, h969, h988, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h993 | h993
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h994 | h994
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h995 | h995
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h996 | h996
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h997 | h997
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h998 | h998
                              · linarith only [h571, h851, h993, h998, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · linarith only [h571, h998, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h847, h994, h997, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h571, h993, h996, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h571, h993, h995, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h571, h993, h994, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1005 | h1005
                      · linarith only [h1005, h993, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1007 | h1007
                        · linarith only [h1007, h571, h851, h993, hc23, hlam, hphi, u2ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1009 | h1009
                          · linarith only [h1007, h1009, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1011 | h1011
                            · linarith only [h1005, h1011, h571, h851, h969, hc24, hlam, hphi, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1013 | h1013
                              · linarith only [h1013, h571, h851, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h1013, h571, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
