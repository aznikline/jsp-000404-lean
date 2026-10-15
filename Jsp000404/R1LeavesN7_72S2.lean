import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_14_25_L_I_L_0_M_IR (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h11, h12, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                          · linarith only [h11, h15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                            · linarith only [h0, h17, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · linarith only [h10, h17, hc24, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h0, h21, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h20, h21, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h10, h20, h8, hc23, hlam, hphi, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                      · linarith only [h25, h8, h9, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h0, h28, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                            · linarith only [h25, h30, hc14, hlam, hphi, u4elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                              · linarith only [h25, h27, h32, h5, h9, hlam]
                              · linarith only [h27, h32, h5, h9, hc34, hlam, hphi, u4elo4]
                        · linarith only [h27, h8, h9, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                    · linarith only [h36, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                        · linarith only [h0, h39, h5, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
                          · linarith only [h0, h36, h41, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                            · linarith only [h0, h43, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · linarith only [h38, h43, h8, hc24, hlam, hphi, u4elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                        · linarith only [h38, h46, h5, h8, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                          · linarith only [h36, h46, h48, hc13, hlam, hphi, ht34, u4elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                            · linarith only [h38, h50, h6, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                              · linarith only [h38, h52, hc14, hlam, hphi, u4elo3]
                              · linarith only [h5, h52, h8, hc23, hlam, hphi, ht34, u4elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                    · linarith only [h0, h4, h5, h56, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                      · linarith only [h0, h4, h58, h6, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                        · linarith only [h0, h4, h5, h60, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h4, h5, h55, h60, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                    · linarith only [h55, h63, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h0, h4, h6, h65, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                        · linarith only [h0, h4, h5, h67, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h69 | h69
                          · linarith only [h5, h63, h69, h7, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                            · linarith only [h6, h65, h7, h71, hlam]
                            · linarith only [h6, h67, h7, h71, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h3, h5, h6, hc23, hlam, hphi, ht34, u4elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                · linarith only [h2, h5, h76, hc02, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                      · linarith only [h0, h2, h5, h75, h80, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h84 | h84
                            · linarith only [h80, h84, hc14, hlam, hphi, u4elo2]
                            · linarith only [h75, h76, h82, h84, hc34, hlam, hphi, u4elo4]
                          · linarith only [h1, h5, h75, h79, h82, h83, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h5, h79, h82, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                      · linarith only [h0, h4, h75, h76, h89, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                          · linarith only [h2, h5, h75, h79, h92, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h94 | h94
                            · linarith only [h89, h94, hc14, hlam, hphi, u4elo2]
                            · linarith only [h5, h75, h91, h92, h94, hc34, hlam, hphi, u4elo4]
                        · linarith only [h5, h91, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h5, h75, h78, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
                · linarith only [h3, h75, h99, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                              · linarith only [h1, h101, h107, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h103, h107, hc34, hlam, hphi, u4elo1]
                            · linarith only [h103, h106, h75, hlam]
                          · linarith only [h102, h105, h5, hlam]
                        · linarith only [h102, h104, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h114 | h114
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h115 | h115
                            · linarith only [h103, h115, h3, hc14, hlam, hphi, u4elo0]
                            · linarith only [h115, h75, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h102, h114, h5, hlam]
                        · linarith only [h101, h102, h113, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                      · linarith only [h101, h102, h120, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                          · linarith only [h0, h101, h102, h123, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h125 | h125
                            · linarith only [h120, h125, h3, hc14, hlam, hphi, u4elo0]
                            · linarith only [h125, h75, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h122, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                    · linarith only [h101, h129, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                        · linarith only [h0, h101, h131, h132, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h132, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                            · linarith only [h101, h131, h137, h3, h5, hc12, hlam, hphi, ht23, ht34, u4elo0]
                            · linarith only [h137, h75, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h101, h135, h136, h5, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h135, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
            · rcases m.htr 1 2 4 (by decide) (by decide) with h143 | h143
              · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                · linarith only [h0, h144, h4, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                    · linarith only [h142, h144, h147, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h149 | h149
                      · linarith only [h142, h144, h146, h149, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                        · linarith only [h142, h144, h149, h151, hc34, hlam, hphi, u4elo4]
                        · linarith only [h142, h144, h146, h149, h151, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
                    · linarith only [h146, h154, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                      · linarith only [h143, h144, h156, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                        · linarith only [h142, h146, h156, h158, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                          · linarith only [h144, h154, h160, h2, h4, hc12, hc25, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h162 | h162
                            · linarith only [h146, h156, h162, hc13, hlam, hphi, ht34, u4elo2]
                            · linarith only [h162, h2, h4, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h142, h143, h3, h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h142, h2, h4, hc12, hc25, hlam, hphi]
        · linarith only [h2, h3, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h168 | h168
        · rcases m.htr 0 2 5 (by decide) (by decide) with h169 | h169
          · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
            · linarith only [h169, h170, h2, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
              · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h175 | h175
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                            · linarith only [h168, h179, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h176, h179, hc24, hlam, hphi, u4elo1]
                          · linarith only [h169, h178, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h172, h176, h177, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
                            · linarith only [h176, h186, hc14, hlam, hphi, u4elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                              · linarith only [h172, h176, h184, h188, hlam]
                              · rcases h2bigk with h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h173, h185, hc02, hlam, hphi, ht0b, ht5b, p190_1, u5ehi3]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h2, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  rcases p190_3 (m.d 0 2) (by simp) with h194 | h194
                                  · rcases p190_3 (m.d 1 2) (by simp) with h195 | h195
                                    · linarith only [h0, h195, hlam]
                                    · linarith only [h172, h195, hlam]
                                  · linarith only [h194, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h185, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u5ehi3]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h0, hlam, p190_1]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h170, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  rcases p190_3 (m.d 0 2) (by simp) with h203 | h203
                                  · rcases p190_3 (m.d 1 2) (by simp) with h204 | h204
                                    · rcases p190_3 (m.d 2 3) (by simp) with h205 | h205
                                      · rcases p190_3 (m.d 2 4) (by simp) with h206 | h206
                                        · linarith only [h206, hlam, p190_0]
                                        · rcases p190_3 (m.d 2 5) (by simp) with h208 | h208
                                          · linarith only [h173, h208, hlam]
                                          · linarith only [h186, h208, hlam]
                                      · linarith only [h184, h205, hlam]
                                    · linarith only [h204, hlam, p190_0]
                                  · linarith only [h168, h203, hlam]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h0, h185, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u5ehi3]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h169, h185, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u5ehi3]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h173, h185, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u5ehi3]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  rcases p190_3 (m.d 0 2) (by simp) with h218 | h218
                                  · linarith only [h2, h218, hlam]
                                  · linarith only [h168, h218, hlam]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  rcases p190_3 (m.d 0 2) (by simp) with h221 | h221
                                  · linarith only [h2, h221, hlam]
                                  · linarith only [h169, h221, hlam]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h168, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h172, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h184, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h186, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h169, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h173, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h185, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h0, h173, h2, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p190_1]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [hlam, p190_0]
                          · linarith only [h0, h173, h185, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h173, h184, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h170, h173, h175, hlam]
                  · linarith only [h170, h173, h174, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi2]
                · linarith only [h169, h173, h2, hc12, hc23, hlam, hphi]
              · linarith only [h168, h172, h2, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
            · linarith only [h0, h2, h240, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h242 | h242
              · rcases m.htr 1 2 5 (by decide) (by decide) with h243 | h243
                · linarith only [h0, h169, h243, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h245 | h245
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h246 | h246
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h247 | h247
                      · linarith only [h242, h243, h247, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h250 | h250
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h251 | h251
                            · linarith only [h0, h169, h242, h247, h250, h251, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h168, h169, h249, h251, hc34, hlam, hphi, u4elo4]
                          · linarith only [h0, h1, h2, h242, h246, h249, h250, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h2, h242, h249, hc24, hlam, hphi, u4elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h256 | h256
                      · linarith only [h240, h242, h246, h256, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h258 | h258
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
                            · linarith only [h240, h242, h246, h256, h259, h260, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h240, h242, h246, h259, h260, hc24, hlam, hphi, u4elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h263 | h263
                            · linarith only [h0, h2, h242, h259, h263, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h0, h169, h242, h258, h263, hc34, hlam, hphi, u4elo4]
                        · linarith only [h0, h2, h242, h258, hc24, hlam, hphi, u4elo3]
                  · linarith only [h240, h242, h245, hc24, hlam, hphi, u4elo3]
              · linarith only [h168, h2, h242, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h269 | h269
          · linarith only [h168, h269, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
            · linarith only [h0, h168, h271, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
              · linarith only [h0, h168, h273, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
                · linarith only [h0, h269, h275, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h278 | h278
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h279 | h279
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h281 | h281
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h282 | h282
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h283 | h283
                              · linarith only [h1, h277, h283, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h273, h279, h283, hc34, hlam, hphi, u4elo2]
                            · linarith only [h273, h279, h282, hlam]
                          · linarith only [h1, h2, h278, h281, hlam]
                        · linarith only [h1, h2, h278, h280, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h289 | h289
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h290 | h290
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h291 | h291
                            · linarith only [h279, h291, hc14, hlam, hphi, u4elo2]
                            · linarith only [h0, h168, h291, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h1, h2, h278, h290, hlam]
                        · linarith only [h1, h2, h277, h278, h289, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h296 | h296
                      · linarith only [h277, h278, h296, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h298 | h298
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h299 | h299
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h300 | h300
                            · linarith only [h296, h300, hc14, hlam, hphi, u4elo2]
                            · linarith only [h0, h168, h300, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h303 | h303
                            · linarith only [h273, h296, h303, hc12, hlam, hphi, ht23, ht34, u4elo2]
                            · linarith only [h0, h168, h303, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h0, h2, h298, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                    · linarith only [h277, h307, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h311 | h311
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h313 | h313
                              · rcases h2bigk with h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h2, hc12, hc23, hlam, hphi, p314_1]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h2, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h168, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h269, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h0, hlam, p314_1]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h271, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h273, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h275, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  rcases p314_3 (m.d 0 2) (by simp) with h325 | h325
                                  · linarith only [h325, hlam, p314_0]
                                  · rcases p314_3 (m.d 1 2) (by simp) with h327 | h327
                                    · linarith only [h271, h327, hlam]
                                    · rcases p314_3 (m.d 2 3) (by simp) with h329 | h329
                                      · rcases p314_3 (m.d 2 4) (by simp) with h330 | h330
                                        · linarith only [h310, h330, hlam]
                                        · linarith only [h168, h330, hlam]
                                      · linarith only [h329, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  rcases p314_3 (m.d 0 2) (by simp) with h334 | h334
                                  · linarith only [h2, h334, hlam]
                                  · linarith only [h0, h334, hlam]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h269, h312, hc02, hc23, hlam, hphi, p314_1]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h271, h307, h311, hc12, hc23, hlam, hphi, p314_1]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, p314_1, u4elo2]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, p314_1, u4elo2]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h310, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h271, h307, h311, hc12, hlam, hphi, ht23, ht34, p314_1, u4elo2]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h0, h312, hc12, hlam, hphi, ht23, ht34, p314_1, u4elo2]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h312, hc12, hlam, hphi, ht23, ht34, p314_1, u4elo2]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h311, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h312, hlam, p314_1]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hlam, p314_0]
                              · linarith only [h277, h309, h313, hlam]
                            · linarith only [h309, h312, hc24, hlam, hphi, u4elo1]
                          · linarith only [h277, h309, h310, h311, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h0, h2, h310, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h354 | h354
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h355 | h355
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h356 | h356
                            · linarith only [h309, h356, hc14, hlam, hphi, u4elo2]
                            · linarith only [h0, h168, h356, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h271, h277, h354, h355, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h2, h354, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h361 | h361
      · linarith only [h0, h1, h361, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h363 | h363
        · rcases m.htr 0 2 5 (by decide) (by decide) with h364 | h364
          · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
            · linarith only [h361, h364, h365, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h367 | h367
              · rcases m.htr 1 2 5 (by decide) (by decide) with h368 | h368
                · linarith only [h0, h1, h365, h368, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h0, h1, h364, h365, h368, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h363, h365, h367, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h372 | h372
            · linarith only [h0, h361, h372, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h374 | h374
              · rcases m.htr 1 2 5 (by decide) (by decide) with h375 | h375
                · linarith only [h0, h364, h375, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h377 | h377
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h378 | h378
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h379 | h379
                      · linarith only [h0, h1, h372, h374, h379, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h381 | h381
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h382 | h382
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
                            · linarith only [h0, h1, h372, h374, h379, h383, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h364, h374, h383, hc24, hlam, hphi, u4elo4]
                          · linarith only [h0, h1, h372, h374, h381, h382, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h372, h374, h381, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h374, h378, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h374, h377, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h363, h364, h374, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h391 | h391
          · linarith only [h363, h391, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h393 | h393
            · linarith only [h0, h363, h393, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h395 | h395
              · linarith only [h0, h363, h395, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h397 | h397
                · linarith only [h0, h391, h397, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h399 | h399
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h400 | h400
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h401 | h401
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h402 | h402
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h403 | h403
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h404 | h404
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h405 | h405
                              · rcases h2bigk with h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h391, h404, hc12, hlam, hphi, ht23, ht34, p406_1, u4elo2]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h361, hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h363, hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h391, hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h0, hlam, p406_1]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h393, hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h395, hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h397, hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  rcases p406_3 (m.d 0 2) (by simp) with h417 | h417
                                  · linarith only [h417, hlam, p406_0]
                                  · rcases p406_3 (m.d 1 2) (by simp) with h419 | h419
                                    · linarith only [h393, h419, hlam]
                                    · rcases p406_3 (m.d 2 3) (by simp) with h421 | h421
                                      · rcases p406_3 (m.d 2 4) (by simp) with h422 | h422
                                        · linarith only [h402, h422, hlam]
                                        · linarith only [h363, h422, hlam]
                                      · linarith only [h421, hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  rcases p406_3 (m.d 0 2) (by simp) with h426 | h426
                                  · linarith only [h361, h426, hlam]
                                  · linarith only [h0, h426, hlam]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h395, h399, h405, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p406_1, u5ehi4]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h391, hc02, hc23, hlam, hphi, p406_1]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, p406_1, u4elo2]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, p406_1, u4elo2]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h402, hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h0, h391, hc12, hlam, hphi, ht23, ht34, p406_1, u4elo2]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h0, h404, hc12, hlam, hphi, ht23, ht34, p406_1, u4elo2]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h404, hc12, hlam, hphi, ht23, ht34, p406_1, u4elo2]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h403, hlam, p406_0]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [h404, hlam, p406_1]
                                · have p406_0 := h406c.1
                                  have p406_1 := h406c.2.1
                                  have p406_2 := h406c.2.2.1
                                  have p406_3 := h406c.2.2.2
                                  linarith only [hlam, p406_0]
                              · linarith only [h395, h401, h405, hc34, hlam, hphi, u4elo2]
                            · linarith only [h0, h363, h404, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h0, h1, h393, h403, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h393, h402, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h447 | h447
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h448 | h448
                            · linarith only [h395, h401, h448, hc12, hlam, hphi, ht23, ht34, u4elo2]
                            · linarith only [h0, h363, h448, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h0, h1, h393, h397, h400, h447, hc12, hc25, hlam, hphi]
                        · linarith only [h0, h1, h393, h446, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h400, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1, h399, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h455 | h455
    · rcases m.htr 0 2 3 (by decide) (by decide) with h456 | h456
      · rcases m.htr 0 2 4 (by decide) (by decide) with h457 | h457
        · rcases m.htr 0 2 5 (by decide) (by decide) with h458 | h458
          · rcases m.htr 1 2 3 (by decide) (by decide) with h459 | h459
            · rcases m.htr 1 2 4 (by decide) (by decide) with h460 | h460
              · rcases m.htr 1 2 5 (by decide) (by decide) with h461 | h461
                · rcases m.htr 1 3 4 (by decide) (by decide) with h462 | h462
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h463 | h463
                    · linarith only [h0, h455, h463, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
                      · linarith only [h0, h455, h462, h465, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h467 | h467
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h468 | h468
                          · linarith only [h459, h463, h468, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h470 | h470
                            · linarith only [h460, h465, h470, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h472 | h472
                              · linarith only [h465, h472, hc14, hlam, hphi, u4elo3]
                              · linarith only [h462, h463, h472, hc34, hlam, hphi, u4elo4]
                        · linarith only [h0, h455, h462, h467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h476 | h476
                    · linarith only [h462, h476, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h478 | h478
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h479 | h479
                        · linarith only [h459, h462, h479, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h481 | h481
                          · linarith only [h457, h476, h479, h481, hc13, hlam, hphi, ht34, u4elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h483 | h483
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h484 | h484
                              · rcases h2bigk with h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h0, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  rcases p485_3 (m.d 0 2) (by simp) with h488 | h488
                                  · rcases p485_3 (m.d 1 2) (by simp) with h489 | h489
                                    · rcases p485_3 (m.d 2 3) (by simp) with h490 | h490
                                      · linarith only [h490, hlam, p485_0]
                                      · rcases p485_3 (m.d 2 4) (by simp) with h492 | h492
                                        · linarith only [h457, h492, hlam]
                                        · linarith only [h479, h492, hlam]
                                    · linarith only [h459, h489, hlam]
                                  · linarith only [h488, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h483, hc02, hlam, hphi, ht0b, ht5b, p485_1, u5ehi4]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  rcases p485_3 (m.d 0 2) (by simp) with h498 | h498
                                  · rcases p485_3 (m.d 1 2) (by simp) with h499 | h499
                                    · rcases p485_3 (m.d 2 3) (by simp) with h500 | h500
                                      · linarith only [h456, h500, hlam]
                                      · rcases p485_3 (m.d 2 4) (by simp) with h502 | h502
                                        · linarith only [h457, h502, hlam]
                                        · linarith only [h483, h502, hlam]
                                    · linarith only [h461, h499, hlam]
                                  · linarith only [h498, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h457, h483, hc12, hlam, hphi, ht01, ht0b, ht5b, p485_1, u5ehi4]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  rcases p485_3 (m.d 0 2) (by simp) with h509 | h509
                                  · linarith only [h0, h509, hlam]
                                  · linarith only [h456, h509, hlam]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h483, hc12, hlam, hphi, ht01, ht0b, ht5b, p485_1, u5ehi4]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  rcases p485_3 (m.d 0 2) (by simp) with h513 | h513
                                  · linarith only [h0, h513, hlam]
                                  · linarith only [h458, h513, hlam]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h456, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h459, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h479, hlam, p485_1]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h481, hlam, p485_1]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h457, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h460, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h460, hc23, hlam, hphi, ht34, p485_1, u4elo1]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h460, h462, h483, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p485_1, u4elo3, u5ehi4]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h458, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h461, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h461, h476, h484, hc23, hlam, hphi, ht34, p485_1, u4elo3]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h483, hlam, p485_1]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [hlam, p485_0]
                              · linarith only [h459, h462, h484, hc23, hlam, hphi, ht34, u4elo4]
                            · linarith only [h478, h483, hc24, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h533 | h533
                        · linarith only [h459, h462, h533, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h535 | h535
                          · linarith only [h0, h455, h459, h476, h535, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h537 | h537
                            · linarith only [h460, h478, h537, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h539 | h539
                              · linarith only [h478, h539, hc14, hlam, hphi, u4elo3]
                              · linarith only [h459, h462, h539, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h0, h455, h458, h459, h461, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h458, h460, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
            · linarith only [h0, h455, h456, h459, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h545 | h545
            · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
              · rcases m.htr 1 2 5 (by decide) (by decide) with h547 | h547
                · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
                  · linarith only [h0, h455, h458, h547, h548, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
                    · linarith only [h0, h455, h458, h547, h550, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h552 | h552
                      · linarith only [h0, h455, h458, h547, h548, h552, hc13, hlam, hphi, ht34, u4elo3]
                      · linarith only [h0, h455, h458, h545, h547, h552, hc23, hlam, hphi, ht34, u4elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h555 | h555
                  · linarith only [h0, h455, h547, h555, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h557 | h557
                    · linarith only [h0, h455, h547, h557, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h559 | h559
                      · linarith only [h0, h455, h545, h547, h555, h559, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h0, h455, h545, h547, h559, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h455, h545, h546, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h0, h456, h545, hlam]
        · linarith only [h0, h455, h457, hc13, hlam, hphi, ht34, u4elo2]
      · linarith only [h0, h455, h456, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h566 | h566
      · rcases m.htr 0 2 4 (by decide) (by decide) with h567 | h567
        · rcases m.htr 0 2 5 (by decide) (by decide) with h568 | h568
          · rcases m.htr 1 2 3 (by decide) (by decide) with h569 | h569
            · rcases m.htr 1 2 4 (by decide) (by decide) with h570 | h570
              · rcases m.htr 1 2 5 (by decide) (by decide) with h571 | h571
                · rcases m.htr 1 3 4 (by decide) (by decide) with h572 | h572
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h573 | h573
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h574 | h574
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h575 | h575
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h577 | h577
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h578 | h578
                              · linarith only [h566, h575, h578, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h570, h577, h578, hc34, hlam, hphi, u4elo1]
                            · linarith only [h574, h577, hc24, hlam, hphi, u4elo1]
                          · linarith only [h573, h574, h575, h576, hc34, hlam, hphi, u4elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h583 | h583
                          · linarith only [h575, h583, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h585 | h585
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h586 | h586
                              · rcases h2bigk with h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h0, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  rcases p587_3 (m.d 0 2) (by simp) with h590 | h590
                                  · rcases p587_3 (m.d 1 2) (by simp) with h591 | h591
                                    · rcases p587_3 (m.d 2 3) (by simp) with h592 | h592
                                      · linarith only [h592, hlam, p587_0]
                                      · rcases p587_3 (m.d 2 4) (by simp) with h594 | h594
                                        · linarith only [h567, h594, hlam]
                                        · linarith only [h575, h594, hlam]
                                    · linarith only [h569, h591, hlam]
                                  · linarith only [h590, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h0, h585, hc12, hlam, hphi, ht01, ht0b, ht5b, p587_1, u5ehi4]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  rcases p587_3 (m.d 0 2) (by simp) with h600 | h600
                                  · rcases p587_3 (m.d 1 2) (by simp) with h601 | h601
                                    · rcases p587_3 (m.d 2 3) (by simp) with h602 | h602
                                      · linarith only [h566, h602, hlam]
                                      · rcases p587_3 (m.d 2 4) (by simp) with h604 | h604
                                        · linarith only [h567, h604, hlam]
                                        · linarith only [h585, h604, hlam]
                                    · linarith only [h571, h601, hlam]
                                  · linarith only [h600, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h567, h585, hc12, hlam, hphi, ht01, ht0b, ht5b, p587_1, u5ehi4]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  rcases p587_3 (m.d 0 2) (by simp) with h611 | h611
                                  · linarith only [h0, h611, hlam]
                                  · linarith only [h566, h611, hlam]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h585, hc12, hlam, hphi, ht01, ht0b, ht5b, p587_1, u5ehi4]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  rcases p587_3 (m.d 0 2) (by simp) with h615 | h615
                                  · linarith only [h0, h615, hlam]
                                  · linarith only [h568, h615, hlam]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h566, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h569, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h575, hlam, p587_1]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h583, hlam, p587_1]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h567, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h570, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, p587_1, u4elo2]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h572, h575, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p587_1, u4elo1, u5ehi2]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h568, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h571, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h571, h574, hc23, hlam, hphi, ht34, p587_1, u4elo1]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h585, hlam, p587_1]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hlam, p587_0]
                              · linarith only [h574, h586, hc34, hlam, hphi, u4elo1]
                            · linarith only [h574, h585, hc24, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h635 | h635
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h637 | h637
                            · linarith only [h574, h637, hc14, hlam, hphi, u4elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h639 | h639
                              · linarith only [h570, h574, h635, h639, hlam]
                              · rcases h2bigk with h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h0, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h636, hc02, hlam, hphi, ht0b, ht5b, p641_1, u5ehi3]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  rcases p641_3 (m.d 0 2) (by simp) with h645 | h645
                                  · rcases p641_3 (m.d 1 2) (by simp) with h646 | h646
                                    · rcases p641_3 (m.d 2 3) (by simp) with h647 | h647
                                      · linarith only [h566, h647, hlam]
                                      · linarith only [h635, h647, hlam]
                                    · linarith only [h570, h646, hlam]
                                  · linarith only [h645, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  rcases p641_3 (m.d 0 2) (by simp) with h652 | h652
                                  · rcases p641_3 (m.d 1 2) (by simp) with h653 | h653
                                    · rcases p641_3 (m.d 2 3) (by simp) with h654 | h654
                                      · linarith only [h566, h654, hlam]
                                      · linarith only [h636, h654, hlam]
                                    · linarith only [h571, h653, hlam]
                                  · linarith only [h652, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h566, h636, hc12, hlam, hphi, ht01, ht0b, ht5b, p641_1, u5ehi3]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h636, hc12, hlam, hphi, ht01, ht0b, ht5b, p641_1, u5ehi3]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  rcases p641_3 (m.d 0 2) (by simp) with h662 | h662
                                  · linarith only [h0, h662, hlam]
                                  · linarith only [h567, h662, hlam]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  rcases p641_3 (m.d 0 2) (by simp) with h665 | h665
                                  · linarith only [h0, h665, hlam]
                                  · linarith only [h568, h665, hlam]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h566, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h569, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  rcases p641_3 (m.d 0 2) (by simp) with h671 | h671
                                  · rcases p641_3 (m.d 1 2) (by simp) with h672 | h672
                                    · rcases p641_3 (m.d 2 3) (by simp) with h673 | h673
                                      · rcases p641_3 (m.d 2 4) (by simp) with h674 | h674
                                        · linarith only [h635, h674, hlam]
                                        · rcases p641_3 (m.d 2 5) (by simp) with h676 | h676
                                          · linarith only [h636, h676, hlam]
                                          · linarith only [h637, h676, hlam]
                                      · linarith only [h635, h673, hlam]
                                    · linarith only [h570, h672, hlam]
                                  · linarith only [h567, h671, hlam]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h566, hc02, hlam, hphi, ht0b, ht5b, p641_1, u5ehi2]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h567, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h570, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h635, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h637, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h568, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h571, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h636, hlam, p641_0]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [h571, h574, h635, hc34, hlam, hphi, p641_1, u4elo4]
                                · have p641_0 := h641c.1
                                  have p641_1 := h641c.2.1
                                  have p641_2 := h641c.2.2.1
                                  have p641_3 := h641c.2.2.2
                                  linarith only [hlam, p641_0]
                          · linarith only [h573, h574, h635, h636, hc34, hlam, hphi, u4elo4]
                        · linarith only [h572, h574, h635, hc23, hlam, hphi, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h695 | h695
                      · linarith only [h572, h573, h695, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h697 | h697
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h698 | h698
                          · linarith only [h455, h573, h698, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h700 | h700
                            · linarith only [h695, h700, hc14, hlam, hphi, u4elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h702 | h702
                              · linarith only [h455, h570, h573, h695, h697, h702, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                              · linarith only [h455, h573, h702, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h572, h573, h697, hc23, hc35, hlam, hphi]
                  · linarith only [h455, h572, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h0, h568, h571, hlam]
              · linarith only [h0, h568, h570, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
            · linarith only [h0, h566, h569, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h710 | h710
            · rcases m.htr 1 2 4 (by decide) (by decide) with h711 | h711
              · rcases m.htr 1 2 5 (by decide) (by decide) with h712 | h712
                · rcases m.htr 1 3 4 (by decide) (by decide) with h713 | h713
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h714 | h714
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h715 | h715
                      · linarith only [h566, h568, h712, h715, hc23, hlam, hphi, ht34, u4elo1]
                      · linarith only [h566, h568, h712, h715, hc23, hlam, hphi, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h718 | h718
                      · linarith only [h566, h568, h712, h718, hc23, hlam, hphi, ht34, u4elo1]
                      · linarith only [h566, h568, h712, h718, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h455, h713, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h722 | h722
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h723 | h723
                    · linarith only [h710, h712, h723, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h725 | h725
                      · linarith only [h710, h712, h722, h725, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h727 | h727
                        · linarith only [h0, h566, h712, h725, h727, hc34, hlam, hphi, u4elo4]
                        · linarith only [h710, h712, h722, h725, h727, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h455, h722, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h567, h711, hlam]
            · linarith only [h0, h566, h710, hlam]
        · linarith only [h566, h567, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h734 | h734
        · rcases m.htr 0 2 5 (by decide) (by decide) with h735 | h735
          · rcases m.htr 1 2 3 (by decide) (by decide) with h736 | h736
            · linarith only [h566, h735, h736, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h738 | h738
              · rcases m.htr 1 2 5 (by decide) (by decide) with h739 | h739
                · rcases m.htr 1 3 4 (by decide) (by decide) with h740 | h740
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h741 | h741
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h742 | h742
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h743 | h743
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h744 | h744
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h745 | h745
                            · linarith only [h0, h734, h736, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h742, h745, hc24, hlam, hphi, u4elo1]
                          · linarith only [h0, h736, h744, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h735, h736, h743, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h750 | h750
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h751 | h751
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h752 | h752
                            · linarith only [h0, h734, h736, h742, h752, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h754 | h754
                              · linarith only [h738, h742, h750, h754, hlam]
                              · rcases h2bigk with h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h0, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h566, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  rcases p756_3 (m.d 0 2) (by simp) with h760 | h760
                                  · rcases p756_3 (m.d 1 2) (by simp) with h761 | h761
                                    · rcases p756_3 (m.d 2 3) (by simp) with h762 | h762
                                      · rcases p756_3 (m.d 2 4) (by simp) with h763 | h763
                                        · linarith only [h763, hlam, p756_0]
                                        · rcases p756_3 (m.d 2 5) (by simp) with h765 | h765
                                          · linarith only [h735, h765, hlam]
                                          · linarith only [h752, h765, hlam]
                                      · linarith only [h750, h762, hlam]
                                    · linarith only [h738, h761, hlam]
                                  · linarith only [h760, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h0, h736, h751, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p756_1, u5ehi3]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h736, hc02, hc23, hlam, hphi, p756_1]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h736, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  rcases p756_3 (m.d 0 2) (by simp) with h775 | h775
                                  · linarith only [h0, h775, hlam]
                                  · linarith only [h734, h775, hlam]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h736, h751, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p756_1, u5ehi3]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h735, h751, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p756_1, u5ehi3]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p756_1]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  rcases p756_3 (m.d 0 2) (by simp) with h782 | h782
                                  · linarith only [h566, h782, hlam]
                                  · linarith only [h734, h782, hlam]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  rcases p756_3 (m.d 0 2) (by simp) with h785 | h785
                                  · linarith only [h566, h785, hlam]
                                  · linarith only [h735, h785, hlam]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h734, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h738, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h750, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h752, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h735, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h739, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h751, hlam, p756_0]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [h0, h735, h736, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p756_1]
                                · have p756_0 := h756c.1
                                  have p756_1 := h756c.2.1
                                  have p756_2 := h756c.2.2.1
                                  have p756_3 := h756c.2.2.2
                                  linarith only [hlam, p756_0]
                          · linarith only [h0, h735, h736, h751, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h735, h736, h750, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h736, h739, h741, hlam]
                  · linarith only [h0, h735, h736, h740, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi2]
                · linarith only [h0, h735, h739, hlam]
              · linarith only [h0, h735, h738, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h804 | h804
            · rcases m.htr 1 2 4 (by decide) (by decide) with h805 | h805
              · rcases m.htr 1 2 5 (by decide) (by decide) with h806 | h806
                · rcases m.htr 1 3 4 (by decide) (by decide) with h807 | h807
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h808 | h808
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h809 | h809
                      · linarith only [h734, h735, h806, h809, hc24, hlam, hphi, u4elo1]
                      · linarith only [h734, h735, h806, h809, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h812 | h812
                      · linarith only [h566, h734, h804, h808, h812, hc24, hlam, hphi, u4elo1]
                      · linarith only [h566, h734, h804, h808, h812, hc24, hlam, hphi, u4elo4]
                  · linarith only [h566, h734, h804, h807, hc24, hlam, hphi, u4elo3]
                · linarith only [h566, h734, h804, h806, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h566, h734, h804, h805, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h818 | h818
              · rcases m.htr 1 2 5 (by decide) (by decide) with h819 | h819
                · linarith only [h734, h735, h804, h819, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h821 | h821
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h822 | h822
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h823 | h823
                      · linarith only [h818, h819, h823, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h825 | h825
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h826 | h826
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h827 | h827
                            · linarith only [h823, h827, hc14, hlam, hphi, u4elo2]
                            · linarith only [h734, h735, h827, hc24, hlam, hphi, u4elo4]
                          · linarith only [h566, h734, h822, h825, h826, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h455, h804, h825, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h832 | h832
                      · linarith only [h804, h818, h822, h832, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h834 | h834
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h835 | h835
                          · linarith only [h0, h804, h822, h835, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h804, h835, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h804, h834, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h804, h821, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h734, h735, h818, hc01, hc25, hlam, hphi, ht12]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h841 | h841
          · linarith only [h734, h841, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h843 | h843
            · rcases m.htr 1 2 4 (by decide) (by decide) with h844 | h844
              · rcases m.htr 1 2 5 (by decide) (by decide) with h845 | h845
                · rcases m.htr 1 3 4 (by decide) (by decide) with h846 | h846
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h847 | h847
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h848 | h848
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h849 | h849
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h850 | h850
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h851 | h851
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h852 | h852
                              · linarith only [h843, h849, h852, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · linarith only [h848, h852, hc34, hlam, hphi, u4elo1]
                            · linarith only [h734, h848, h851, hc04, hlam, hphi, u4elo1]
                          · linarith only [h0, h566, h843, h847, h850, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h566, h849, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h734, h844, h848, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h859 | h859
                      · linarith only [h846, h847, h859, hlam]
                      · linarith only [h0, h734, h844, h859, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h566, h843, h846, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h0, h566, h843, h845, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h566, h843, h844, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h865 | h865
              · linarith only [h0, h734, h843, h865, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h865, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

end R2N4
