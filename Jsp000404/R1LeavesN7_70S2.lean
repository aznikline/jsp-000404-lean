import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_I_L_R_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
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
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h10, h11, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h17 | h17
                          · linarith only [h10, h17, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                              · linarith only [h0, h10, h20, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h0, h19, h20, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h10, h16, h19, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
                          · linarith only [h16, h24, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                              · linarith only [h0, h10, h27, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h26, h27, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                              · linarith only [h0, h26, h30, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                                · linarith only [h2, h32, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                                  · linarith only [h0, h26, h34, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                                    · linarith only [h30, h34, h36, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                                      · linarith only [h0, h26, h32, h34, h38, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h40 | h40
                                        · linarith only [h0, h10, h34, h38, h4, h40, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                        · linarith only [h26, h40, hc45, hlam, hphi, ht34, u3ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                          · linarith only [h0, h45, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h0, h43, h45, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h43, h44, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                          · linarith only [h43, h50, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                              · linarith only [h1, h53, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h0, h4, h52, h53, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h52, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
                          · linarith only [h49, h57, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h59 | h59
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
                              · linarith only [h1, h60, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h0, h4, h59, h60, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h59, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h65, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                          · linarith only [h0, h70, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h0, h6, h68, h70, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h5, h68, h69, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                          · linarith only [h4, h68, h7, h75, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                            · linarith only [h4, h68, h7, h77, hlam]
                            · linarith only [h4, h68, h7, h74, h77, hc34, hlam, hphi, u3ehi1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                          · linarith only [h74, h80, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                            · linarith only [h1, h7, h82, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                              · linarith only [h1, h65, h84, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                                · linarith only [h0, h5, h74, h86, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h67, h7, h82, h86, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h91 | h91
                          · linarith only [h0, h91, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h0, h6, h89, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h5, h89, h90, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                        · linarith only [h4, h67, h7, h89, h95, hc24, hc45, hlam, hphi]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                          · linarith only [h4, h67, h7, h89, h97, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                            · linarith only [h1, h67, h7, h99, hc45, hlam, hphi, ht34, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h101 | h101
                              · linarith only [h1, h101, h65, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                                · linarith only [h103, h4, h67, h7, h89, h95, hc12, hc24, hlam, hphi]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                                  · linarith only [h105, h4, h7, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                                    · linarith only [h107, h4, h65, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h109 | h109
                                      · linarith only [h109, h5, h67, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h111 | h111
                                        · linarith only [h111, h4, h67, h7, h89, hc12, hc34, hlam, hphi, ht23]
                                        · linarith only [h111, h4, h7, h89, hc12, hc45, hlam, hphi, ht23, ht34]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
                · rcases m.htr 0 3 5 (by decide) (by decide) with h115 | h115
                  · linarith only [h115, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h114, h115, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h118 | h118
                  · linarith only [h114, h118, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
                    · linarith only [h120, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                          · linarith only [h0, h124, h6, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                            · linarith only [h1, h114, h126, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                              · linarith only [h0, h1, h114, h118, h122, h128, h6, hc34, hlam, hphi, u3ehi2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                                · linarith only [h120, h130, h2, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                                  · linarith only [h0, h122, h132, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h134 | h134
                                    · linarith only [h0, h118, h123, h132, h134, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                                    · linarith only [h134, h4, h6, hc35, hlam, hphi, u3ehi2]
                        · linarith only [h122, h123, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h122, h4, h6, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h139 | h139
              · linarith only [h139, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h141 | h141
                · linarith only [h141, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h143 | h143
                  · linarith only [h141, h143, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h145 | h145
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h147 | h147
                        · linarith only [h0, h147, h5, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h149 | h149
                          · linarith only [h0, h139, h149, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
                            · linarith only [h1, h141, h151, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                              · linarith only [h1, h143, h153, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                                · linarith only [h155, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h145, h146, h147, h155, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h146, h4, h5, hc12, hc24, hlam, hphi]
                    · linarith only [h145, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h160 | h160
            · rcases m.htr 0 2 5 (by decide) (by decide) with h161 | h161
              · linarith only [h161, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h163 | h163
                · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
                    · linarith only [h160, h165, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
                      · linarith only [h0, h160, h167, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                          · linarith only [h0, h161, h170, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                              · linarith only [h1, h173, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h164, h172, h173, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h163, h165, h172, hc45, hlam, hphi, ht34, u3ehi1]
                        · linarith only [h160, h161, h169, hc12, hc25, hlam, hphi]
                  · linarith only [h163, h164, hc35, hlam, hphi, u3ehi3]
                · linarith only [h160, h163, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h180 | h180
              · linarith only [h160, h180, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h182 | h182
                · rcases m.htr 0 3 5 (by decide) (by decide) with h183 | h183
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h184 | h184
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h185 | h185
                      · linarith only [h0, h185, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h187 | h187
                        · linarith only [h0, h160, h187, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
                          · linarith only [h0, h180, h189, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                              · linarith only [h1, h192, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h191, h192, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h195 | h195
                              · linarith only [h182, h191, h195, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h197 | h197
                                · linarith only [h197, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h199 | h199
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h200 | h200
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h201 | h201
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h202 | h202
                                        · linarith only [h182, h191, h197, h202, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                        · linarith only [h184, h191, h202, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                      · linarith only [h160, h182, h184, h201, h4, hc02, hc23, hlam, hphi]
                                    · linarith only [h182, h184, h200, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                  · linarith only [h182, h199, h4, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
                      · linarith only [h0, h208, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
                        · linarith only [h0, h160, h210, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h212 | h212
                          · linarith only [h0, h160, h212, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h215 | h215
                              · linarith only [h1, h215, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h183, h214, h215, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h182, h184, h214, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h182, h183, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h220 | h220
                  · linarith only [h182, h220, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h222 | h222
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h223 | h223
                      · linarith only [h0, h223, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
                        · linarith only [h0, h160, h225, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h227 | h227
                          · linarith only [h0, h180, h227, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                            · linarith only [h1, h182, h229, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h231 | h231
                              · linarith only [h1, h220, h231, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h233 | h233
                                · linarith only [h2, h233, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h182, h222, h229, h233, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h236 | h236
                      · linarith only [h0, h236, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h238 | h238
                        · linarith only [h0, h160, h238, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
                          · linarith only [h0, h180, h240, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h242 | h242
                            · linarith only [h1, h182, h222, h242, hc45, hlam, hphi, ht34, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h244 | h244
                              · linarith only [h1, h220, h244, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
                                · linarith only [h182, h2, h222, h246, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h248 | h248
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h249 | h249
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h251 | h251
                                        · linarith only [h1, h182, h222, h251, hc34, hlam, hphi, u3ehi1]
                                        · linarith only [h1, h182, h248, h250, h251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                      · linarith only [h1, h182, h248, h250, hc45, hlam, hphi, ht34, u3ehi1]
                                    · linarith only [h1, h182, h248, h249, hc35, hlam, hphi, u3ehi1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h256 | h256
                                    · linarith only [h248, h256, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                                      · linarith only [h1, h182, h222, h248, h258, hc34, hlam, hphi, u3ehi1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h260 | h260
                                        · linarith only [h0, h160, h258, h260, hc12, hc34, hlam, hphi, ht23]
                                        · linarith only [h1, h182, h260, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h263 | h263
          · rcases m.htr 0 2 4 (by decide) (by decide) with h264 | h264
            · rcases m.htr 0 2 5 (by decide) (by decide) with h265 | h265
              · linarith only [h0, h265, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h267 | h267
                · rcases m.htr 0 3 5 (by decide) (by decide) with h268 | h268
                  · linarith only [h0, h263, h268, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h267, h268, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h271 | h271
                  · linarith only [h0, h264, h267, h271, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h273 | h273
                    · linarith only [h0, h264, h273, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
                      · linarith only [h0, h275, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h263, h265, h275, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h278 | h278
              · linarith only [h264, h278, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h280 | h280
                · linarith only [h263, h264, h280, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h282 | h282
                  · linarith only [h280, h282, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h284 | h284
                    · linarith only [h2, h284, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h263, h264, h284, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h287 | h287
            · rcases m.htr 0 2 5 (by decide) (by decide) with h288 | h288
              · linarith only [h263, h288, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h290 | h290
                · rcases m.htr 0 3 5 (by decide) (by decide) with h291 | h291
                  · linarith only [h1, h291, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h290, h291, hc35, hlam, hphi, u3ehi3]
                · linarith only [h263, h287, h290, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h295 | h295
              · linarith only [h287, h295, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h297 | h297
                · rcases m.htr 0 3 5 (by decide) (by decide) with h298 | h298
                  · linarith only [h1, h298, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h297, h298, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h301 | h301
                  · linarith only [h297, h301, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h303 | h303
                    · linarith only [h2, h3, h303, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h305 | h305
                      · linarith only [h0, h3, h305, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h307 | h307
                        · linarith only [h0, h287, h3, h307, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h309 | h309
                          · linarith only [h0, h295, h3, h309, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h311 | h311
                            · linarith only [h1, h3, h309, h311, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h313 | h313
                              · linarith only [h2, h3, h309, h311, h313, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · linarith only [h2, h3, h311, h313, hc35, hlam, hphi, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h316 | h316
        · linarith only [h2, h316, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h318 | h318
          · rcases m.htr 0 2 4 (by decide) (by decide) with h319 | h319
            · linarith only [h0, h2, h319, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h321 | h321
              · linarith only [h0, h316, h321, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h323 | h323
                · linarith only [h0, h2, h318, h323, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h325 | h325
                  · linarith only [h1, h316, h325, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h327 | h327
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h328 | h328
                      · linarith only [h0, h316, h328, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h318, h319, h328, hc12, hc24, hlam, hphi]
                    · linarith only [h0, h2, h318, h327, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h332 | h332
            · linarith only [h1, h2, h318, h332, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h334 | h334
              · linarith only [h318, h334, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h336 | h336
                · linarith only [h1, h2, h336, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h338 | h338
                  · linarith only [h336, h338, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h340 | h340
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                      · linarith only [h0, h2, h318, h341, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h343 | h343
                        · linarith only [h0, h332, h340, h343, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h345 | h345
                          · linarith only [h1, h2, h334, h341, h343, h345, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h347 | h347
                            · linarith only [h1, h2, h318, h336, h343, h347, hc02, hc24, hlam, hphi]
                            · linarith only [h1, h2, h347, hc34, hlam, hphi, u3ehi1]
                    · linarith only [h1, h2, h340, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h351 | h351
      · rcases m.htr 0 1 5 (by decide) (by decide) with h352 | h352
        · linarith only [h1, h352, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h354 | h354
          · linarith only [h0, h1, h354, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h356 | h356
            · rcases m.htr 0 2 5 (by decide) (by decide) with h357 | h357
              · linarith only [h0, h1, h357, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h359 | h359
                · rcases m.htr 0 3 5 (by decide) (by decide) with h360 | h360
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h361 | h361
                    · linarith only [h1, h351, h361, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
                      · linarith only [h0, h1, h354, h363, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h366 | h366
                          · linarith only [h0, h352, h357, h366, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h368 | h368
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h369 | h369
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
                                · linarith only [h351, h352, h363, h369, h370, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                · linarith only [h0, h352, h365, h370, hc24, hc45, hlam, hphi]
                              · linarith only [h0, h1, h360, h365, h368, h369, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1, h368, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h354, h356, h365, hc12, hc23, hlam, hphi]
                  · linarith only [h359, h360, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h1, h356, h359, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h378 | h378
              · linarith only [h1, h351, h356, h378, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h380 | h380
                · rcases m.htr 0 3 5 (by decide) (by decide) with h381 | h381
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h382 | h382
                    · linarith only [h1, h351, h382, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                      · linarith only [h0, h1, h354, h384, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h386 | h386
                        · linarith only [h0, h1, h356, h380, h384, h386, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h388 | h388
                          · linarith only [h1, h351, h378, h384, h386, h388, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                                · linarith only [h351, h352, h384, h391, h392, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                · linarith only [h351, h352, h390, h392, hc45, hlam, hphi, ht34, u3ehi3]
                              · linarith only [h1, h351, h381, h386, h391, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h1, h351, h386, h390, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h380, h381, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h351, h380, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h399 | h399
        · linarith only [h1, h399, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h401 | h401
          · linarith only [h0, h1, h401, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h403 | h403
            · linarith only [h0, h351, h403, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h405 | h405
              · linarith only [h0, h351, h405, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h407 | h407
                · rcases m.htr 0 3 5 (by decide) (by decide) with h408 | h408
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h409 | h409
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h410 | h410
                      · linarith only [h0, h351, h410, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h412 | h412
                        · linarith only [h0, h1, h403, h410, h412, hc02, hc23, hlam, hphi]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h414 | h414
                          · linarith only [h0, h399, h405, h414, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h416 | h416
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h417 | h417
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h418 | h418
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h422 | h422
                                        · linarith only [h407, h422, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                        · rcases h0bigk with h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [hlam, p424_0]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h399, h410, h416, h418, hc02, hc23, hlam, hphi, p424_1]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h1, hlam, p424_0]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h351, hlam, p424_1]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h399, hlam, p424_1]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h0, hlam, p424_0]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [hlam, p424_0]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h401, hlam, p424_0]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h403, hlam, p424_1]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h405, hlam, p424_0]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h0, h1, h410, hc12, hc23, hlam, hphi, p424_1]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            rcases p424_3 (m.d 0 1) (by simp) with h436 | h436
                                            · linarith only [h1, h436, hlam]
                                            · linarith only [h0, h436, hlam]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [hlam, p424_0]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h1, h409, h410, h422, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p424_1, u3ehi3]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h1, h409, h410, h422, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p424_1, u3ehi3]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h0, h351, h410, h416, hc12, hc23, hlam, hphi, p424_1]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            rcases p424_3 (m.d 0 1) (by simp) with h443 | h443
                                            · linarith only [h351, h443, hlam]
                                            · linarith only [h0, h443, hlam]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h407, hlam, p424_0]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [hlam, p424_0]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h351, h409, h410, h416, h422, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p424_1, u3ehi3]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h0, h399, h410, h416, h418, hc12, hc23, hlam, hphi, p424_1]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            rcases p424_3 (m.d 0 1) (by simp) with h450 | h450
                                            · linarith only [h399, h450, hlam]
                                            · linarith only [h0, h450, hlam]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h408, hlam, p424_0]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [h409, hlam, p424_1]
                                          · have p424_0 := h424c.1
                                            have p424_1 := h424c.2.1
                                            have p424_2 := h424c.2.2.1
                                            have p424_3 := h424c.2.2.2
                                            linarith only [hlam, p424_0]
                                      · linarith only [h403, h409, h421, hlam]
                                    · linarith only [h0, h1, h410, h420, hc12, hc35, hlam, hphi, ht23]
                                  · linarith only [h1, h407, h409, h410, h419, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · linarith only [h351, h409, h418, hlam]
                              · linarith only [h1, h408, h417, hlam]
                            · linarith only [h1, h407, h416, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
                      · linarith only [h0, h351, h462, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h464 | h464
                        · linarith only [h0, h351, h409, h464, hc24, hc45, hlam, hphi]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h466 | h466
                          · linarith only [h0, h466, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h468 | h468
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h469 | h469
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h470 | h470
                                · linarith only [h0, h351, h409, h462, h468, h470, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h351, h470, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h0, h1, h408, h469, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h1, h408, h468, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · linarith only [h407, h408, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h476 | h476
                  · linarith only [h407, h476, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h478 | h478
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
                      · linarith only [h0, h399, h479, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h481 | h481
                        · linarith only [h0, h1, h403, h407, h478, h481, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h483 | h483
                          · linarith only [h0, h1, h407, h483, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h485 | h485
                            · linarith only [h0, h1, h407, h479, h485, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h485, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                      · linarith only [h0, h1, h488, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                        · linarith only [h0, h1, h407, h478, h490, hc24, hc45, hlam, hphi]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                          · linarith only [h0, h1, h407, h478, h492, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
                            · linarith only [h0, h1, h407, h488, h494, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h494, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h497 | h497
    · rcases m.htr 0 1 4 (by decide) (by decide) with h498 | h498
      · rcases m.htr 0 1 5 (by decide) (by decide) with h499 | h499
        · linarith only [h0, h499, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h501 | h501
          · rcases m.htr 0 2 4 (by decide) (by decide) with h502 | h502
            · rcases m.htr 0 2 5 (by decide) (by decide) with h503 | h503
              · rcases m.htr 0 3 4 (by decide) (by decide) with h504 | h504
                · rcases m.htr 0 3 5 (by decide) (by decide) with h505 | h505
                  · linarith only [h0, h497, h505, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h504, h505, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h508 | h508
                  · linarith only [h504, h508, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h510 | h510
                    · linarith only [h0, h498, h510, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h513 | h513
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h514 | h514
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h515 | h515
                            · linarith only [h497, h499, h514, h515, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h517 | h517
                              · linarith only [h498, h499, h508, h514, h515, h517, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · linarith only [h497, h499, h512, h517, hc35, hlam, hphi, u3ehi2]
                          · linarith only [h0, h497, h503, h512, h514, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h497, h512, h513, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h497, h512, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h523 | h523
                · rcases m.htr 0 3 5 (by decide) (by decide) with h524 | h524
                  · linarith only [h0, h497, h524, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h523, h524, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h527 | h527
                  · linarith only [h0, h498, h503, h523, h527, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h529 | h529
                    · linarith only [h0, h498, h503, h529, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h531 | h531
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h532 | h532
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h533 | h533
                          · linarith only [h0, h497, h503, h531, h533, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h0, h497, h531, h533, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h497, h531, h532, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h497, h531, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h0, h498, h502, hlam]
          · linarith only [h0, h497, h501, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h540 | h540
        · linarith only [h498, h540, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h542 | h542
          · rcases m.htr 0 2 4 (by decide) (by decide) with h543 | h543
            · rcases m.htr 0 2 5 (by decide) (by decide) with h544 | h544
              · rcases m.htr 0 3 4 (by decide) (by decide) with h545 | h545
                · linarith only [h497, h498, h545, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h547 | h547
                  · linarith only [h545, h547, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h549 | h549
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h550 | h550
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h551 | h551
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h552 | h552
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h553 | h553
                            · linarith only [h497, h498, h545, h551, h553, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h497, h498, h550, h553, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h497, h498, h550, h551, h552, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h497, h543, h550, h551, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h544, h550, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · linarith only [h497, h498, h549, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h560 | h560
                · linarith only [h497, h498, h560, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h562 | h562
                  · linarith only [h560, h562, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h564 | h564
                    · linarith only [h543, h544, h564, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h497, h498, h564, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h567 | h567
              · linarith only [h543, h567, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h569 | h569
                · linarith only [h0, h497, h543, h569, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h571 | h571
                  · linarith only [h0, h497, h543, h571, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h575 | h575
                        · linarith only [h0, h497, h543, h574, h575, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h497, h574, h575, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h497, h574, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h497, h498, h573, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h497, h542, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h581 | h581
      · rcases m.htr 0 1 5 (by decide) (by decide) with h582 | h582
        · linarith only [h0, h582, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h584 | h584
          · rcases m.htr 0 2 4 (by decide) (by decide) with h585 | h585
            · rcases m.htr 0 2 5 (by decide) (by decide) with h586 | h586
              · rcases m.htr 0 3 4 (by decide) (by decide) with h587 | h587
                · rcases m.htr 0 3 5 (by decide) (by decide) with h588 | h588
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h589 | h589
                    · linarith only [h0, h581, h589, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h591 | h591
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h592 | h592
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h593 | h593
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h594 | h594
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h595 | h595
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h596 | h596
                                · linarith only [h581, h582, h589, h591, h595, h596, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h581, h582, h594, h596, hc45, hlam, hphi, ht34, u3ehi3]
                              · linarith only [h497, h581, h584, h588, h595, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h497, h581, h587, h588, h594, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h497, h588, h591, h593, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h497, h588, h591, h592, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h584, h591, hlam]
                  · linarith only [h587, h588, hc35, hlam, hphi, u3ehi3]
                · linarith only [h497, h581, h587, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h606 | h606
                · rcases m.htr 0 3 5 (by decide) (by decide) with h607 | h607
                  · linarith only [h584, h586, h607, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h606, h607, hc35, hlam, hphi, u3ehi3]
                · linarith only [h497, h581, h606, hlam]
            · linarith only [h0, h581, h585, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h612 | h612
            · rcases m.htr 0 2 5 (by decide) (by decide) with h613 | h613
              · linarith only [h584, h613, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h615 | h615
                · rcases m.htr 0 3 5 (by decide) (by decide) with h616 | h616
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h617 | h617
                    · linarith only [h0, h581, h584, h617, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h619 | h619
                      · linarith only [h584, h616, h619, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h621 | h621
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h622 | h622
                          · linarith only [h613, h619, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h624 | h624
                            · linarith only [h0, h581, h619, h624, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h615, h617, h624, hc45, hlam, hphi, ht34, u3ehi1]
                        · linarith only [h0, h581, h612, h621, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h615, h616, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h581, h584, h615, hlam]
            · linarith only [h0, h581, h612, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h631 | h631
        · linarith only [h0, h631, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h633 | h633
          · rcases m.htr 0 2 4 (by decide) (by decide) with h634 | h634
            · rcases m.htr 0 2 5 (by decide) (by decide) with h635 | h635
              · rcases m.htr 0 3 4 (by decide) (by decide) with h636 | h636
                · rcases m.htr 0 3 5 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h638 | h638
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h639 | h639
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h640 | h640
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h641 | h641
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h642 | h642
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h643 | h643
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h644 | h644
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h645 | h645
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h646 | h646
                                    · linarith only [h633, h646, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                    · linarith only [h645, h646, hc35, hlam, hphi, u3ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h649 | h649
                                    · linarith only [h497, h636, h639, h645, h649, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h651 | h651
                                      · linarith only [h0, h634, h651, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h653 | h653
                                        · linarith only [h645, h651, h653, hc34, hlam, hphi, u3ehi2]
                                        · linarith only [h581, h638, h639, h642, h645, h653, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · linarith only [h581, h638, h644, hlam]
                              · linarith only [h581, h638, h642, h643, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h497, h636, h638, h642, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h0, h633, h635, h636, h638, h641, hc05, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h0, h633, h636, h638, h640, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h633, h636, h638, h639, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h663 | h663
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h664 | h664
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h665 | h665
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h666 | h666
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h667 | h667
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h669 | h669
                                    · linarith only [h633, h669, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                    · linarith only [h637, h638, h662, h665, h667, h668, h669, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h636, h638, h662, h665, h667, h668, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h673 | h673
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h674 | h674
                                    · linarith only [h0, h633, h674, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                    · linarith only [h0, h633, h637, h673, h674, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h581, h636, h667, h673, hc45, hlam, hphi, ht34, u3ehi2]
                              · linarith only [h0, h497, h633, h637, h666, hc01, hc12, hlam, hphi]
                            · linarith only [h497, h636, h638, h665, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h0, h633, h637, h664, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h633, h634, h637, h638, h663, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                      · linarith only [h0, h633, h637, h662, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h636, h637, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h684 | h684
                  · linarith only [h636, h684, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h686 | h686
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h687 | h687
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h688 | h688
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h689 | h689
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h690 | h690
                            · linarith only [h636, h686, h690, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h692 | h692
                              · linarith only [h684, h690, h692, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h694 | h694
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h695 | h695
                                  · linarith only [h497, h690, h695, hc01, hc23, hlam, hphi, ht12]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h697 | h697
                                    · linarith only [h497, h633, h692, h697, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h699 | h699
                                      · linarith only [h0, h634, h699, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                      · linarith only [h581, h686, h690, h695, h699, hc34, hlam, hphi, u3ehi2]
                                · linarith only [h581, h686, h694, hlam]
                          · linarith only [h0, h631, h634, h635, h686, h689, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · linarith only [h0, h635, h688, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h634, h686, h687, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h706 | h706
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h707 | h707
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h708 | h708
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h709 | h709
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h710 | h710
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h711 | h711
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h712 | h712
                                  · linarith only [h633, h636, h712, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h714 | h714
                                    · linarith only [h633, h636, h686, h706, h709, h711, h714, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h716 | h716
                                      · linarith only [h634, h686, h716, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h718 | h718
                                        · linarith only [h633, h636, h686, h718, hc34, hlam, hphi, u3ehi2]
                                        · linarith only [h633, h636, h706, h709, h711, h718, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · linarith only [h633, h636, h709, h711, hc45, hlam, hphi, ht34, u3ehi2]
                              · linarith only [h633, h636, h709, h710, hc35, hlam, hphi, u3ehi2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h723 | h723
                              · linarith only [h709, h723, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h725 | h725
                                · linarith only [h633, h636, h686, h709, h725, hc34, hlam, hphi, u3ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h727 | h727
                                  · linarith only [h581, h633, h636, h725, h727, hc45, hlam, hphi, ht34, u3ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h729 | h729
                                    · linarith only [h634, h723, h727, h729, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h731 | h731
                                      · linarith only [h581, h634, h725, h731, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h733 | h733
                                        · linarith only [h581, h636, h725, h733, hc34, hlam, hphi, u3ehi0]
                                        · linarith only [h633, h636, h733, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h0, h635, h708, hlam]
                        · linarith only [h0, h634, h635, h707, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h633, h635, h706, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h739 | h739
                · rcases m.htr 0 3 5 (by decide) (by decide) with h740 | h740
                  · linarith only [h633, h635, h740, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h739, h740, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h743 | h743
                  · linarith only [h634, h635, h739, h743, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h745 | h745
                    · linarith only [h634, h635, h745, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h747 | h747
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h748 | h748
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h749 | h749
                          · linarith only [h633, h635, h749, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h751 | h751
                            · linarith only [h739, h747, h749, h751, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h753 | h753
                              · linarith only [h743, h751, h753, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h755 | h755
                                · linarith only [h748, h749, h755, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h757 | h757
                                  · linarith only [h0, h633, h749, h757, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h759 | h759
                                    · linarith only [h0, h634, h749, h757, h759, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                    · linarith only [h0, h634, h749, h757, h759, hc35, hlam, hphi, u3ehi2]
                        · linarith only [h0, h634, h748, hlam]
                      · linarith only [h0, h633, h747, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h764 | h764
              · linarith only [h634, h764, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h766 | h766
                · linarith only [h633, h634, h766, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h768 | h768
                  · linarith only [h633, h634, h768, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h770 | h770
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h771 | h771
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h772 | h772
                        · linarith only [h633, h634, h772, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h774 | h774
                          · linarith only [h633, h764, h772, h774, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h776 | h776
                            · linarith only [h766, h770, h776, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h778 | h778
                              · linarith only [h768, h776, h778, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h780 | h780
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h781 | h781
                                  · linarith only [h0, h633, h772, h776, h781, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h0, h633, h772, h781, hc34, hlam, hphi, u3ehi2]
                                · linarith only [h581, h770, h780, hlam]
                      · linarith only [h0, h633, h771, hlam]
                    · linarith only [h633, h634, h770, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h787 | h787
            · rcases m.htr 0 2 5 (by decide) (by decide) with h788 | h788
              · linarith only [h633, h788, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h790 | h790
                · rcases m.htr 0 3 5 (by decide) (by decide) with h791 | h791
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h792 | h792
                    · linarith only [h633, h787, h792, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h794 | h794
                      · linarith only [h633, h791, h794, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h796 | h796
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h797 | h797
                          · linarith only [h788, h794, h797, hc02, hc23, hlam, hphi]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h799 | h799
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h800 | h800
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h801 | h801
                                · linarith only [h794, h796, h801, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h803 | h803
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h804 | h804
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h805 | h805
                                      · linarith only [h0, h787, h797, h801, h804, h805, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                      · linarith only [h0, h787, h797, h803, h805, hc45, hlam, hphi, ht34, u3ehi3]
                                    · linarith only [h633, h787, h803, h804, hc35, hlam, hphi, u3ehi3]
                                  · linarith only [h0, h794, h803, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h497, h791, h800, hlam]
                            · linarith only [h497, h790, h791, h799, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h787, h796, hlam]
                  · linarith only [h790, h791, hc35, hlam, hphi, u3ehi3]
                · linarith only [h633, h787, h790, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h815 | h815
              · linarith only [h787, h815, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h817 | h817
                · rcases m.htr 0 3 5 (by decide) (by decide) with h818 | h818
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h819 | h819
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h820 | h820
                      · linarith only [h633, h817, h819, h820, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h822 | h822
                        · linarith only [h787, h820, h822, hc02, hc23, hlam, hphi]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h824 | h824
                          · linarith only [h815, h818, h820, h824, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h826 | h826
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h827 | h827
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h828 | h828
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h829 | h829
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h830 | h830
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h831 | h831
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h832 | h832
                                        · linarith only [h817, h832, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                        · rcases h0bigk with h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [hlam, p834_0]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h0, hlam, p834_1]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h497, hlam, p834_0]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h581, hlam, p834_1]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h631, hlam, p834_1]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h0, h824, h829, h831, hc01, hc23, hlam, hphi, ht12, p834_1]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [hlam, p834_0]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h633, hlam, p834_0]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h787, hlam, p834_1]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h815, hlam, p834_0]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            rcases p834_3 (m.d 0 1) (by simp) with h845 | h845
                                            · linarith only [h497, h845, hlam]
                                            · rcases p834_3 (m.d 0 2) (by simp) with h847 | h847
                                              · linarith only [h633, h847, hlam]
                                              · linarith only [h0, h847, hlam]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            rcases p834_3 (m.d 0 1) (by simp) with h850 | h850
                                            · linarith only [h497, h850, hlam]
                                            · rcases p834_3 (m.d 0 2) (by simp) with h852 | h852
                                              · linarith only [h633, h852, hlam]
                                              · rcases p834_3 (m.d 0 3) (by simp) with h854 | h854
                                                · rcases p834_3 (m.d 0 4) (by simp) with h855 | h855
                                                  · linarith only [h817, h855, hlam]
                                                  · linarith only [h787, h855, hlam]
                                                · linarith only [h633, h854, hlam]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [hlam, p834_0]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h497, h819, h820, h832, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p834_1, u3ehi3]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h497, h819, h820, h832, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p834_1, u3ehi3]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            rcases p834_3 (m.d 0 1) (by simp) with h862 | h862
                                            · linarith only [h581, h862, hlam]
                                            · rcases p834_3 (m.d 0 2) (by simp) with h864 | h864
                                              · linarith only [h787, h864, hlam]
                                              · linarith only [h0, h864, hlam]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            rcases p834_3 (m.d 0 1) (by simp) with h867 | h867
                                            · linarith only [h581, h867, hlam]
                                            · rcases p834_3 (m.d 0 2) (by simp) with h869 | h869
                                              · linarith only [h787, h869, hlam]
                                              · rcases p834_3 (m.d 0 3) (by simp) with h871 | h871
                                                · rcases p834_3 (m.d 0 4) (by simp) with h872 | h872
                                                  · rcases p834_3 (m.d 0 5) (by simp) with h873 | h873
                                                    · linarith only [h819, h873, hlam]
                                                    · linarith only [h815, h873, hlam]
                                                  · linarith only [h787, h872, hlam]
                                                · linarith only [h633, h871, hlam]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h817, hlam, p834_0]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [hlam, p834_0]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h819, h832, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p834_1, u3ehi3]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            rcases p834_3 (m.d 0 1) (by simp) with h881 | h881
                                            · linarith only [h631, h881, hlam]
                                            · rcases p834_3 (m.d 0 2) (by simp) with h883 | h883
                                              · linarith only [h815, h883, hlam]
                                              · linarith only [h0, h883, hlam]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            rcases p834_3 (m.d 0 1) (by simp) with h886 | h886
                                            · linarith only [h631, h886, hlam]
                                            · rcases p834_3 (m.d 0 2) (by simp) with h888 | h888
                                              · linarith only [h815, h888, hlam]
                                              · rcases p834_3 (m.d 0 3) (by simp) with h890 | h890
                                                · rcases p834_3 (m.d 0 4) (by simp) with h891 | h891
                                                  · rcases p834_3 (m.d 0 5) (by simp) with h892 | h892
                                                    · rcases h2bigk with h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h0, hlam, p893_1]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h633, hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h787, hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h815, hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h0, h824, h829, h831, hc01, hc23, hlam, hphi, ht12, p893_1]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h820, hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h822, hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h824, hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        rcases p893_3 (m.d 0 2) (by simp) with h904 | h904
                                                        · linarith only [h904, hlam, p893_0]
                                                        · rcases p893_3 (m.d 1 2) (by simp) with h906 | h906
                                                          · linarith only [h820, h906, hlam]
                                                          · linarith only [h0, h906, hlam]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p893_1]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h831, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p893_1, u5ehi2]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h0, h631, h824, hc01, hc23, hlam, hphi, ht12, p834_1, p893_1]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        rcases p893_3 (m.d 0 2) (by simp) with h913 | h913
                                                        · linarith only [h913, hlam, p893_0]
                                                        · rcases p893_3 (m.d 1 2) (by simp) with h915 | h915
                                                          · linarith only [h822, h915, hlam]
                                                          · linarith only [h0, h915, hlam]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p893_1]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h829, hlam, p893_1]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h0, h631, h824, h829, hc01, hc23, hlam, hphi, ht12, p834_1, p893_1]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        rcases p893_3 (m.d 0 2) (by simp) with h922 | h922
                                                        · linarith only [h922, hlam, p893_0]
                                                        · rcases p893_3 (m.d 1 2) (by simp) with h924 | h924
                                                          · linarith only [h824, h924, hlam]
                                                          · linarith only [h0, h924, hlam]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p893_1]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h830, hlam, p893_1]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [h831, hlam, p893_0]
                                                      · have p893_0 := h893c.1
                                                        have p893_1 := h893c.2.1
                                                        have p893_2 := h893c.2.2.1
                                                        have p893_3 := h893c.2.2.2
                                                        linarith only [hlam, p893_0]
                                                    · linarith only [h815, h892, hlam]
                                                  · linarith only [h787, h891, hlam]
                                                · linarith only [h633, h890, hlam]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h818, hlam, p834_0]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [h819, hlam, p834_1]
                                          · have p834_0 := h834c.1
                                            have p834_1 := h834c.2.1
                                            have p834_2 := h834c.2.2.1
                                            have p834_3 := h834c.2.2.2
                                            linarith only [hlam, p834_0]
                                      · linarith only [h787, h819, h831, hlam]
                                    · linarith only [h581, h819, h820, h826, h830, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                  · linarith only [h581, h819, h820, h826, h829, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · linarith only [h581, h819, h828, hlam]
                              · linarith only [h497, h818, h827, hlam]
                            · linarith only [h497, h817, h826, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h943 | h943
                      · linarith only [h633, h818, h943, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h945 | h945
                        · linarith only [h0, h787, h943, h945, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h947 | h947
                          · linarith only [h943, h947, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h949 | h949
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h950 | h950
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h951 | h951
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h952 | h952
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h953 | h953
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h954 | h954
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h955 | h955
                                        · linarith only [h817, h819, h955, hlam]
                                        · rcases h0bigk with h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [hlam, p957_0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h0, hlam, p957_1]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h497, hlam, p957_0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h581, hlam, p957_1]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h631, hlam, p957_1]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h0, h947, h952, h954, hc01, hc23, hlam, hphi, ht12, p957_1]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [hlam, p957_0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h633, hlam, p957_0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h787, hlam, p957_1]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h815, hlam, p957_0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            rcases p957_3 (m.d 0 1) (by simp) with h968 | h968
                                            · linarith only [h497, h968, hlam]
                                            · rcases p957_3 (m.d 0 2) (by simp) with h970 | h970
                                              · linarith only [h633, h970, hlam]
                                              · linarith only [h0, h970, hlam]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            rcases p957_3 (m.d 0 1) (by simp) with h973 | h973
                                            · linarith only [h497, h973, hlam]
                                            · rcases p957_3 (m.d 0 2) (by simp) with h975 | h975
                                              · linarith only [h633, h975, hlam]
                                              · rcases p957_3 (m.d 0 3) (by simp) with h977 | h977
                                                · rcases p957_3 (m.d 0 4) (by simp) with h978 | h978
                                                  · linarith only [h817, h978, hlam]
                                                  · linarith only [h787, h978, hlam]
                                                · linarith only [h633, h977, hlam]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [hlam, p957_0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            rcases p957_3 (m.d 0 1) (by simp) with h983 | h983
                                            · linarith only [h497, h983, hlam]
                                            · rcases p957_3 (m.d 0 2) (by simp) with h985 | h985
                                              · linarith only [h633, h985, hlam]
                                              · rcases p957_3 (m.d 0 3) (by simp) with h987 | h987
                                                · rcases p957_3 (m.d 0 4) (by simp) with h988 | h988
                                                  · linarith only [h817, h988, hlam]
                                                  · rcases p957_3 (m.d 0 5) (by simp) with h990 | h990
                                                    · linarith only [h818, h990, hlam]
                                                    · linarith only [h819, h990, hlam]
                                                · linarith only [h817, h987, hlam]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [hc03, hlam, hphi, ht0b, ht5b, p957_1, u5ehi0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h819, h943, h949, h951, hc01, hc23, hlam, hphi, ht12, p957_1]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h819, h943, h949, h951, hc02, hc23, hlam, hphi, p957_1]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h817, hlam, p957_0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [hlam, p957_0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h819, hlam, p957_0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h819, h943, h949, h951, hc01, hc23, hlam, hphi, ht12, p957_1]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h0, h819, h943, h949, h951, hc01, hc23, hlam, hphi, ht12, p957_1]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h818, hlam, p957_0]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [h817, h819, h943, h949, h951, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p957_1, u3ehi3]
                                          · have p957_0 := h957c.1
                                            have p957_1 := h957c.2.1
                                            have p957_2 := h957c.2.2.1
                                            have p957_3 := h957c.2.2.2
                                            linarith only [hlam, p957_0]
                                      · linarith only [h0, h787, h943, h949, h951, h954, hc01, hc23, hlam, hphi, ht12]
                                    · linarith only [h819, h943, h949, h951, h953, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                  · linarith only [h817, h819, h943, h949, h951, h952, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1008 | h1008
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1009 | h1009
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1010 | h1010
                                      · linarith only [h0, h1010, h945, h951, hc01, hc24, hlam, hphi, ht12]
                                      · linarith only [h0, h1010, h945, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                    · linarith only [h1009, h497, h818, h943, hlam]
                                  · linarith only [h1008, h497, h581, h817, h818, h943, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · linarith only [h497, h818, h950, hlam]
                            · linarith only [h497, h817, h818, h819, h949, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                  · linarith only [h817, h818, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1018 | h1018
                  · linarith only [h1018, h817, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1020 | h1020
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1021 | h1021
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1022 | h1022
                        · linarith only [h1020, h1022, h787, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · linarith only [h0, h1021, h1022, h633, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1025 | h1025
                        · linarith only [h0, h1021, h1025, h787, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1027 | h1027
                          · linarith only [h1021, h1027, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1029 | h1029
                            · linarith only [h1020, h1029, h817, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1031 | h1031
                              · linarith only [h1029, h1031, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1033 | h1033
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1034 | h1034
                                  · linarith only [h0, h1021, h1029, h1034, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h1021, h1034, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h1020, h1033, h581, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1038 | h1038
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1039 | h1039
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1040 | h1040
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1041 | h1041
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1042 | h1042
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1043 | h1043
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1044 | h1044
                                  · linarith only [h1038, h1044, h817, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                  · linarith only [h0, h1038, h1041, h1044, h633, hc01, hc12, hlam, hphi]
                                · linarith only [h1041, h1043, h817, hc45, hlam, hphi, ht34, u3ehi0]
                              · linarith only [h1041, h1042, h817, hc35, hlam, hphi, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1049 | h1049
                              · linarith only [h1041, h1049, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1051 | h1051
                                · linarith only [h1020, h1041, h1051, h817, hc34, hlam, hphi, u3ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1053 | h1053
                                  · linarith only [h1038, h1041, h1051, h1053, hc45, hlam, hphi, ht34, u3ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1055 | h1055
                                    · linarith only [h1049, h1055, h497, hc01, hc23, hlam, hphi, ht12]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1057 | h1057
                                      · linarith only [h1039, h1051, h1057, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1059 | h1059
                                        · linarith only [h1051, h1059, h581, hc01, hc34, hlam, hphi, ht12, ht23]
                                        · linarith only [h1059, h817, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h0, h1038, h1040, h633, hc01, hc25, hlam, hphi, ht12]
                        · linarith only [h0, h1038, h1039, h633, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1064 | h1064
                        · linarith only [h0, h1038, h1064, h787, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1066 | h1066
                          · linarith only [h1038, h1066, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1068 | h1068
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1069 | h1069
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1070 | h1070
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1071 | h1071
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1072 | h1072
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1073 | h1073
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1074 | h1074
                                        · linarith only [h1020, h1074, h817, hc34, hlam, hphi, u3ehi0]
                                        · linarith only [h1038, h1068, h1070, h1074, h817, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                                      · linarith only [h0, h1038, h1068, h1070, h1073, h787, hc01, hc23, hlam, hphi, ht12]
                                    · linarith only [h1038, h1069, h1072, hlam]
                                  · linarith only [h1038, h1069, h1071, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                · linarith only [h1068, h1070, h817, hc45, hlam, hphi, ht34, u3ehi0]
                              · linarith only [h1068, h1069, h817, hc35, hlam, hphi, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1082 | h1082
                              · linarith only [h1068, h1082, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1084 | h1084
                                · linarith only [h1020, h1068, h1084, h817, hc34, hlam, hphi, u3ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1086 | h1086
                                  · linarith only [h0, h1038, h1068, h1086, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h1038, h1086, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
