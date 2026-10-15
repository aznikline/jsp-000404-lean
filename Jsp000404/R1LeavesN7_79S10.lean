import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_LR_L_R_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h4, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h11, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14 | h14
                · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h15, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h18, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
            · linarith only [h4, h5, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
            · linarith only [h22, h4, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                  · linarith only [h26, h4, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                    · linarith only [h1, h26, h28, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                      · linarith only [h1, h22, h26, h30, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                        · linarith only [h1, h32, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h2, h32, h34, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                          · linarith only [h1, h24, h26, h34, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                  · linarith only [h37, h4, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                    · linarith only [h0, h39, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
                      · linarith only [h1, h22, h37, h41, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                        · linarith only [h1, h43, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                          · linarith only [h2, h43, h45, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                          · linarith only [h1, h24, h37, h45, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h48 | h48
                · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                  · linarith only [h4, h49, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                    · linarith only [h0, h51, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                      · linarith only [h1, h22, h49, h53, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
                        · linarith only [h1, h55, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                          · linarith only [h2, h24, h55, h57, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                              · linarith only [h49, h55, h60, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h2, h4, h49, h57, h59, h60, hc34, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1]
                            · linarith only [h2, h48, h51, h59, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
                  · linarith only [h4, h64, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
                    · linarith only [h1, h64, h66, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
                      · linarith only [h1, h22, h64, h68, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h70 | h70
                        · linarith only [h1, h70, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h72 | h72
                          · linarith only [h2, h24, h4, h70, h72, hlam, hphi, u0ehi6, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
                            · linarith only [h2, h48, h74, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                              · linarith only [h64, h70, h76, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h3, h4, h64, h70, h74, h76, hc34, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h79 | h79
          · rcases m.htr 0 2 5 (by decide) (by decide) with h80 | h80
            · linarith only [h0, h3, h80, hlam]
            · linarith only [h79, h80, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h83 | h83
            · linarith only [h79, h83, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h85 | h85
              · linarith only [h1, h3, h85, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h87 | h87
                · linarith only [h2, h3, h87, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
                  · linarith only [h0, h89, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                    · linarith only [h0, h3, h91, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
                      · linarith only [h1, h3, h83, h89, h93, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi0]
                      · linarith only [h1, h3, h89, h93, hc25, hlam, hphi, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h96 | h96
        · rcases m.htr 0 2 3 (by decide) (by decide) with h97 | h97
          · rcases m.htr 0 2 5 (by decide) (by decide) with h98 | h98
            · rcases m.htr 0 3 5 (by decide) (by decide) with h99 | h99
              · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
                · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                  · linarith only [h0, h101, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi2]
                  · linarith only [h0, h101, h2, h97, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                · linarith only [h0, h100, h2, h97, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h105 | h105
                · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
                  · linarith only [h0, h106, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h106, h2, h97, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                · linarith only [h1, h105, h2, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h97, h98, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h111 | h111
            · linarith only [h111, h97, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h113 | h113
              · rcases m.htr 0 4 5 (by decide) (by decide) with h114 | h114
                · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                  · linarith only [h115, h97, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                    · linarith only [h1, h115, h117, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · linarith only [h1, h115, h117, h2, hc24, hlam, hphi, u2ehi1]
                · linarith only [h1, h114, h2, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                  · linarith only [h0, h122, h97, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                    · linarith only [h1, h122, h124, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                    · linarith only [h1, h122, h124, h2, hc24, hlam, hphi, u2ehi1]
                · linarith only [h0, h121, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h128 | h128
          · rcases m.htr 0 2 5 (by decide) (by decide) with h129 | h129
            · linarith only [h0, h129, h96, hlam]
            · linarith only [h128, h129, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h132 | h132
            · linarith only [h128, h132, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h134 | h134
              · linarith only [h1, h134, h96, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h136 | h136
                · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                  · linarith only [h0, h136, h137, h96, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
                    · linarith only [h1, h136, h137, h139, h96, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                    · linarith only [h1, h137, h139, h2, hc24, hlam, hphi, u2ehi1]
                · linarith only [h1, h136, h2, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h143 | h143
      · rcases m.htr 0 1 5 (by decide) (by decide) with h144 | h144
        · rcases m.htr 0 2 3 (by decide) (by decide) with h145 | h145
          · linarith only [h0, h1, h145, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h147 | h147
            · linarith only [h145, h147, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
              · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
                · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                  · linarith only [h145, h151, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h1, h151, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
                  · linarith only [h0, h154, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h1, h154, hc23, hlam, hphi, u2ehi1]
              · linarith only [h0, h1, h149, hc35, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h158 | h158
          · linarith only [h0, h1, h158, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h160 | h160
            · linarith only [h158, h160, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h162 | h162
              · rcases m.htr 0 4 5 (by decide) (by decide) with h163 | h163
                · linarith only [h143, h144, h163, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
                  · linarith only [h158, h165, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h1, h165, hc23, hlam, hphi, u2ehi1]
              · linarith only [h0, h1, h162, hc35, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h169 | h169
        · rcases m.htr 0 2 3 (by decide) (by decide) with h170 | h170
          · linarith only [h0, h1, h170, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h172 | h172
            · linarith only [h170, h172, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h174 | h174
              · rcases m.htr 0 4 5 (by decide) (by decide) with h175 | h175
                · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
                  · linarith only [h170, h176, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h1, h176, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h143, h175, hc45, hlam, hphi, ht23, ht34, u2ehi1]
              · linarith only [h0, h1, h174, hc35, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h181 | h181
          · linarith only [h0, h1, h181, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h183 | h183
            · linarith only [h181, h183, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h185 | h185
              · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
                · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
                  · linarith only [h181, h187, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h1, h187, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h143, h186, hc45, hlam, hphi, ht23, ht34, u2ehi1]
              · linarith only [h0, h1, h185, hc35, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h192 | h192
    · rcases m.htr 0 1 4 (by decide) (by decide) with h193 | h193
      · rcases m.htr 0 1 5 (by decide) (by decide) with h194 | h194
        · rcases m.htr 0 2 3 (by decide) (by decide) with h195 | h195
          · rcases m.htr 0 2 5 (by decide) (by decide) with h196 | h196
            · rcases m.htr 0 3 5 (by decide) (by decide) with h197 | h197
              · rcases m.htr 0 4 5 (by decide) (by decide) with h198 | h198
                · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h200 | h200
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
                        · linarith only [h192, h202, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
                          · linarith only [h0, h193, h202, h204, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                          · linarith only [h0, h192, h197, h204, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                      · linarith only [h0, h201, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h200, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h192, h195, h197, h199, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h212 | h212
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h213 | h213
                        · linarith only [h192, h213, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h215 | h215
                          · linarith only [h0, h193, h213, h215, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h197, h215, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h212, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h192, h210, h211, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h192, h210, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
                · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
                        · linarith only [h192, h225, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
                          · linarith only [h0, h193, h197, h225, h227, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                              · linarith only [h222, h225, h230, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                                · linarith only [h0, h193, h197, h222, h227, h229, h232, hc12, hlam, hphi, ht01, u0ehi7]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h234 | h234
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h235 | h235
                                    · rcases h5bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [hlam, p236_0]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h0, h193, h221, h222, h227, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi2]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h0, h193, h221, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi4]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h197, hlam, p236_0]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        rcases p236_3 (m.d 0 5) (by simp) with h241 | h241
                                        · rcases p236_3 (m.d 1 5) (by simp) with h242 | h242
                                          · linarith only [h194, h242, hlam]
                                          · linarith only [h229, h242, hlam]
                                        · linarith only [h221, h241, hlam]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h194, hlam, p236_0]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [hlam, p236_0]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h0, h194, h232, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi2]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h227, hlam, p236_0]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h0, h193, h229, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p236_1]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h196, hlam, p236_1]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h224, hlam, p236_1]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [hlam, p236_0]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h232, hlam, p236_1]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h196, hc45, hlam, hphi, ht0b, ht5b, p236_1, u0elo1]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h235, hc34, hlam, hphi, ht01, ht12, ht23, p236_1, u0ehi9]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h224, h235, hc34, hlam, hphi, ht23, p236_1, u2ehi4]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h235, hc34, hlam, hphi, ht23, p236_1, u2ehi4]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [hlam, p236_0]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        rcases p236_3 (m.d 0 5) (by simp) with h260 | h260
                                        · linarith only [h197, h260, hlam]
                                        · linarith only [h221, h260, hlam]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h221, hlam, p236_1]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h229, hlam, p236_1]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h234, hlam, p236_1]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [h235, hlam, p236_1]
                                      · have p236_0 := h236c.1
                                        have p236_1 := h236c.2.1
                                        have p236_2 := h236c.2.2.1
                                        have p236_3 := h236c.2.2.2
                                        linarith only [hlam, p236_0]
                                    · linarith only [h0, h193, h221, h235, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h0, h193, h229, h234, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h193, h221, h223, h229, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h224, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h192, h222, h223, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h192, h222, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h275 | h275
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h276 | h276
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                        · linarith only [h192, h277, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                          · linarith only [h0, h193, h277, h279, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                            · linarith only [h0, h193, h221, h281, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
                              · linarith only [h274, h277, h283, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h285 | h285
                                · linarith only [h0, h194, h197, h274, h277, h281, h285, hc12, hlam, hphi, ht01, u0ehi7]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h287 | h287
                                  · linarith only [h0, h194, h221, h275, h281, h287, hc12, hlam, hphi, ht01, u0ehi8]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h289 | h289
                                    · linarith only [h221, h289, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                    · linarith only [h274, h277, h289, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h276, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h192, h274, h275, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h192, h274, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h195, h196, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h192, h195, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h297 | h297
          · rcases m.htr 0 2 5 (by decide) (by decide) with h298 | h298
            · rcases m.htr 0 3 5 (by decide) (by decide) with h299 | h299
              · linarith only [h192, h194, h299, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h301 | h301
                · linarith only [h193, h194, h301, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                        · linarith only [h192, h306, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h308 | h308
                          · linarith only [h193, h194, h298, h299, h306, h308, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                          · linarith only [h193, h194, h306, h308, hc35, hlam, hphi, u3ehi1]
                      · linarith only [h298, h305, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                    · linarith only [h0, h192, h303, h304, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h192, h303, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h297, h298, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h192, h297, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h316 | h316
        · rcases m.htr 0 2 3 (by decide) (by decide) with h317 | h317
          · rcases m.htr 0 2 5 (by decide) (by decide) with h318 | h318
            · rcases m.htr 0 3 5 (by decide) (by decide) with h319 | h319
              · rcases m.htr 0 4 5 (by decide) (by decide) with h320 | h320
                · rcases m.htr 1 2 3 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h322 | h322
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h323 | h323
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h324 | h324
                        · linarith only [h192, h324, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h192, h193, h324, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h192, h193, h321, h322, h323, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h192, h321, h322, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h192, h321, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h192, h193, h319, h320, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
                · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h333 | h333
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h335 | h335
                        · linarith only [h192, h193, h333, h335, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h192, h193, h332, h335, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h192, h193, h332, h333, h334, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h192, h332, h333, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h192, h332, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h192, h193, h331, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h317, h318, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h192, h317, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h344 | h344
          · rcases m.htr 0 2 5 (by decide) (by decide) with h345 | h345
            · rcases m.htr 0 3 5 (by decide) (by decide) with h346 | h346
              · linarith only [h192, h316, h346, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h348 | h348
                · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h350 | h350
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h351 | h351
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h352 | h352
                        · linarith only [h192, h352, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h192, h193, h349, h352, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h192, h193, h345, h349, h350, h351, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h0, h192, h349, h350, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h192, h349, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h192, h193, h348, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h344, h345, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h192, h344, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h361 | h361
      · rcases m.htr 0 1 5 (by decide) (by decide) with h362 | h362
        · rcases m.htr 0 2 3 (by decide) (by decide) with h363 | h363
          · rcases m.htr 0 2 5 (by decide) (by decide) with h364 | h364
            · rcases m.htr 0 3 5 (by decide) (by decide) with h365 | h365
              · rcases m.htr 0 4 5 (by decide) (by decide) with h366 | h366
                · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h368 | h368
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h369 | h369
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h370 | h370
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h371 | h371
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h372 | h372
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h373 | h373
                              · linarith only [h363, h373, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                              · linarith only [h361, h370, h373, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                            · linarith only [h192, h361, h366, h367, h370, h372, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h192, h371, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                        · linarith only [h192, h361, h368, h370, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h192, h361, h367, h368, h369, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h192, h367, h368, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h361, h366, h367, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h382 | h382
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h383 | h383
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h384 | h384
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h385 | h385
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h386 | h386
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h387 | h387
                            · linarith only [h361, h366, h387, hlam, hphi, u0ehi8, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h389 | h389
                              · linarith only [h363, h389, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                              · linarith only [h192, h362, h382, h385, h387, h389, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h192, h386, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                        · linarith only [h192, h362, h384, h385, hc34, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h192, h382, h384, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h192, h362, h366, h382, h383, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                  · linarith only [h0, h362, h366, h382, hc23, hlam, hphi, ht01, ht12, u0ehi8]
              · linarith only [h192, h362, h365, hlam]
            · linarith only [h363, h364, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h399 | h399
            · linarith only [h363, h399, hc23, hlam, hphi, u2ehi4]
            · linarith only [h0, h362, h399, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h402 | h402
          · rcases m.htr 0 2 5 (by decide) (by decide) with h403 | h403
            · rcases m.htr 0 3 5 (by decide) (by decide) with h404 | h404
              · rcases m.htr 0 4 5 (by decide) (by decide) with h405 | h405
                · linarith only [h361, h362, h405, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h407 | h407
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h410 | h410
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
                            · linarith only [h361, h405, h412, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h361, h362, h408, h412, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                          · linarith only [h402, h404, h411, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · linarith only [h192, h361, h408, h410, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h192, h361, h403, h407, h408, h409, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                    · linarith only [h192, h407, h408, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h361, h407, hc23, hlam, hphi, ht01, ht12, u0ehi8]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h420 | h420
                · linarith only [h361, h362, h420, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h422 | h422
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                    · linarith only [h192, h361, h404, h423, hc35, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h192, h422, h423, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h402, h422, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h402, h403, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h428 | h428
            · linarith only [h402, h428, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h430 | h430
              · rcases m.htr 0 4 5 (by decide) (by decide) with h431 | h431
                · linarith only [h0, h361, h428, h431, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h433 | h433
                  · linarith only [h0, h361, h402, h433, hc12, hlam, hphi, ht01, u0ehi8]
                  · linarith only [h0, h361, h433, hc23, hlam, hphi, ht01, ht12, u0ehi8]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
                · linarith only [h192, h361, h430, h436, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h438 | h438
                  · linarith only [h0, h361, h402, h438, hc12, hlam, hphi, ht01, u0ehi8]
                  · linarith only [h0, h361, h438, hc23, hlam, hphi, ht01, ht12, u0ehi8]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h441 | h441
        · rcases m.htr 0 2 3 (by decide) (by decide) with h442 | h442
          · rcases m.htr 0 2 5 (by decide) (by decide) with h443 | h443
            · rcases m.htr 0 3 5 (by decide) (by decide) with h444 | h444
              · rcases m.htr 0 4 5 (by decide) (by decide) with h445 | h445
                · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h447 | h447
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h448 | h448
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h449 | h449
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h450 | h450
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h451 | h451
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h452 | h452
                              · linarith only [h442, h452, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h454 | h454
                                · linarith only [h446, h449, h452, h454, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h444, h454, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · linarith only [h361, h441, h448, h451, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                          · linarith only [h449, h450, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h192, h441, h448, h449, hc34, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h0, h448, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h192, h441, h446, h447, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h0, h441, h446, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h361, h441, h445, hlam]
              · linarith only [h192, h441, h444, hlam]
            · linarith only [h442, h443, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h466 | h466
            · linarith only [h442, h466, hc23, hlam, hphi, u2ehi4]
            · linarith only [h0, h441, h466, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h469 | h469
          · rcases m.htr 0 2 5 (by decide) (by decide) with h470 | h470
            · rcases m.htr 0 3 5 (by decide) (by decide) with h471 | h471
              · rcases m.htr 0 4 5 (by decide) (by decide) with h472 | h472
                · rcases m.htr 1 2 3 (by decide) (by decide) with h473 | h473
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h474 | h474
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h475 | h475
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h476 | h476
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h478 | h478
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h479 | h479
                              · linarith only [h469, h479, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h481 | h481
                                · linarith only [h473, h476, h479, h481, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h471, h481, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · linarith only [h361, h472, h478, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h469, h471, h477, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · linarith only [h192, h476, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h470, h475, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                    · linarith only [h192, h473, h474, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h473, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h491 | h491
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h494 | h494
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h495 | h495
                            · linarith only [h472, h490, h493, h495, hc12, hlam, hphi, ht01, u0ehi8]
                            · linarith only [h361, h495, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                          · linarith only [h469, h471, h494, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · linarith only [h192, h493, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h470, h492, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                    · linarith only [h192, h490, h491, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h469, h490, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h503 | h503
                · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h506 | h506
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h507 | h507
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h508 | h508
                          · linarith only [h471, h504, h508, hc12, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h507, h508, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h192, h507, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h470, h506, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                    · linarith only [h192, h504, h505, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h469, h504, hlam, hphi, u0ehi5, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h515 | h515
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h516 | h516
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h517 | h517
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h518 | h518
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h519 | h519
                          · linarith only [h192, h471, h515, h519, hc12, hlam, hphi, ht01, u0ehi5]
                          · linarith only [h518, h519, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h192, h518, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h470, h517, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                    · linarith only [h192, h515, h516, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h469, h515, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h469, h470, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h527 | h527
            · linarith only [h469, h527, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h529 | h529
              · rcases m.htr 0 4 5 (by decide) (by decide) with h530 | h530
                · rcases m.htr 1 2 3 (by decide) (by decide) with h531 | h531
                  · linarith only [h469, h531, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h531, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h534 | h534
                  · linarith only [h469, h534, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h534, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h537 | h537
                · rcases m.htr 1 2 3 (by decide) (by decide) with h538 | h538
                  · linarith only [h0, h469, h538, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h538, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h541 | h541
                  · linarith only [h0, h469, h541, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h541, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem r1l7_22_14_M_LI_L_0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4elo := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · linarith only [h12, h3, hc34, hlam, hphi, u4elo0]
                        · linarith only [h11, h3, hc24, hlam, hphi, u4elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h10, h16, h9, hlam]
                        · linarith only [h16, h3, hc24, hlam, hphi, u4elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h19, h4, h7, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                          · rcases h2bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h19, h22, h4, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p23_1, u2elo0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              rcases p23_3 (m.d 0 2) (by simp) with h26 | h26
                              · rcases p23_3 (m.d 1 2) (by simp) with h27 | h27
                                · rcases p23_3 (m.d 2 3) (by simp) with h28 | h28
                                  · linarith only [h28, hlam, p23_0]
                                  · rcases p23_3 (m.d 2 4) (by simp) with h30 | h30
                                    · linarith only [h1, h30, hlam]
                                    · linarith only [h30, h9, hlam]
                                · linarith only [h27, h4, hlam]
                              · linarith only [h26, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h21, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23_1, u2elo0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              rcases p23_3 (m.d 0 2) (by simp) with h36 | h36
                              · rcases p23_3 (m.d 1 2) (by simp) with h37 | h37
                                · rcases p23_3 (m.d 2 3) (by simp) with h38 | h38
                                  · linarith only [h0, h38, hlam]
                                  · rcases p23_3 (m.d 2 4) (by simp) with h40 | h40
                                    · linarith only [h1, h40, hlam]
                                    · linarith only [h21, h40, hlam]
                                · linarith only [h37, h6, hlam]
                              · linarith only [h36, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [hc02, hlam, hphi, p23_1, u2elo1]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              rcases p23_3 (m.d 0 2) (by simp) with h47 | h47
                              · rcases p23_3 (m.d 1 2) (by simp) with h48 | h48
                                · rcases p23_3 (m.d 2 3) (by simp) with h49 | h49
                                  · linarith only [h49, hlam, p23_0]
                                  · rcases p23_3 (m.d 2 4) (by simp) with h51 | h51
                                    · linarith only [h5, h51, hlam]
                                    · linarith only [h51, h9, hlam]
                                · linarith only [h48, hlam, p23_0]
                              · linarith only [h0, h47, hlam]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h21, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23_1, u2elo1]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              rcases p23_3 (m.d 0 2) (by simp) with h57 | h57
                              · rcases p23_3 (m.d 1 2) (by simp) with h58 | h58
                                · rcases p23_3 (m.d 2 3) (by simp) with h59 | h59
                                  · linarith only [h4, h59, hlam]
                                  · rcases p23_3 (m.d 2 4) (by simp) with h61 | h61
                                    · linarith only [h5, h61, hlam]
                                    · linarith only [h21, h61, hlam]
                                · linarith only [h58, hlam, p23_0]
                              · linarith only [h2, h57, hlam]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h0, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h4, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h9, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h19, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h1, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h5, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, p23_1, u4elo2]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h19, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p23_1, u2elo1]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h2, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h6, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p23_1, u2elo0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [h21, hlam, p23_0]
                            · have p23_0 := h23c.1
                              have p23_1 := h23c.2.1
                              have p23_2 := h23c.2.2.1
                              have p23_3 := h23c.2.2.2
                              linarith only [hlam, p23_0]
                          · linarith only [h22, h3, h9, hc24, hlam, hphi, u4elo0]
                        · linarith only [h21, h3, h9, hc23, hlam, hphi, ht34, u4elo0]
                  · linarith only [h3, h8, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                    · linarith only [h4, h7, h85, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h87 | h87
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h88 | h88
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                          · rcases h2bigk with h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [hc12, hlam, hphi, p90_1, u2elo0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h87, h89, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p90_1, u2elo0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h85, h87, h89, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p90_1, u2elo0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              rcases p90_3 (m.d 0 2) (by simp) with h95 | h95
                              · rcases p90_3 (m.d 1 2) (by simp) with h96 | h96
                                · rcases p90_3 (m.d 2 3) (by simp) with h97 | h97
                                  · linarith only [h0, h97, hlam]
                                  · linarith only [h87, h97, hlam]
                                · linarith only [h6, h96, hlam]
                              · linarith only [h95, hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [hc02, hlam, hphi, p90_1, u2elo1]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h87, h89, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p90_1, u2elo1]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h85, h87, h89, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p90_1, u2elo1]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              rcases p90_3 (m.d 0 2) (by simp) with h106 | h106
                              · rcases p90_3 (m.d 1 2) (by simp) with h107 | h107
                                · rcases p90_3 (m.d 2 3) (by simp) with h108 | h108
                                  · linarith only [h108, h4, hlam]
                                  · linarith only [h108, h87, hlam]
                                · linarith only [h107, hlam, p90_0]
                              · linarith only [h106, h2, hlam]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h0, hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h4, hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h85, hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h4, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p90_1, u4elo3]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h1, hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h5, hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h87, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p90_1, u2elo3]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h1, h87, h89, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p90_1, u2elo0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h2, hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h6, hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h87, hlam, p90_1]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [h88, hlam, p90_0]
                            · have p90_0 := h90c.1
                              have p90_1 := h90c.2.1
                              have p90_2 := h90c.2.2.1
                              have p90_3 := h90c.2.2.2
                              linarith only [hlam, p90_0]
                          · linarith only [h7, h89, hc13, hlam, hphi, ht34, u4elo4]
                        · linarith only [h84, h88, hc24, hlam, hphi, u4elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                          · rcases h2bigk with h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [hc12, hlam, hphi, p132_1, u2elo0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              rcases p132_3 (m.d 0 2) (by simp) with h135 | h135
                              · rcases p132_3 (m.d 1 2) (by simp) with h136 | h136
                                · rcases p132_3 (m.d 2 3) (by simp) with h137 | h137
                                  · linarith only [h137, hlam, p132_0]
                                  · rcases p132_3 (m.d 2 4) (by simp) with h139 | h139
                                    · linarith only [h1, h139, hlam]
                                    · linarith only [h139, h85, hlam]
                                · linarith only [h136, h4, hlam]
                              · linarith only [h135, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h130, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p132_1, u2elo0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              rcases p132_3 (m.d 0 2) (by simp) with h145 | h145
                              · rcases p132_3 (m.d 1 2) (by simp) with h146 | h146
                                · rcases p132_3 (m.d 2 3) (by simp) with h147 | h147
                                  · linarith only [h0, h147, hlam]
                                  · rcases p132_3 (m.d 2 4) (by simp) with h149 | h149
                                    · linarith only [h1, h149, hlam]
                                    · linarith only [h130, h149, hlam]
                                · linarith only [h146, h6, hlam]
                              · linarith only [h145, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [hc02, hlam, hphi, p132_1, u2elo1]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              rcases p132_3 (m.d 0 2) (by simp) with h156 | h156
                              · rcases p132_3 (m.d 1 2) (by simp) with h157 | h157
                                · rcases p132_3 (m.d 2 3) (by simp) with h158 | h158
                                  · linarith only [h158, hlam, p132_0]
                                  · rcases p132_3 (m.d 2 4) (by simp) with h160 | h160
                                    · linarith only [h160, h5, hlam]
                                    · linarith only [h160, h85, hlam]
                                · linarith only [h157, hlam, p132_0]
                              · linarith only [h0, h156, hlam]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h130, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p132_1, u2elo1]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              rcases p132_3 (m.d 0 2) (by simp) with h166 | h166
                              · rcases p132_3 (m.d 1 2) (by simp) with h167 | h167
                                · rcases p132_3 (m.d 2 3) (by simp) with h168 | h168
                                  · linarith only [h168, h4, hlam]
                                  · rcases p132_3 (m.d 2 4) (by simp) with h170 | h170
                                    · linarith only [h170, h5, hlam]
                                    · linarith only [h130, h170, hlam]
                                · linarith only [h167, hlam, p132_0]
                              · linarith only [h166, h2, hlam]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h0, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h4, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h85, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h87, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h1, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h5, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h5, hc23, hlam, hphi, ht34, p132_1, u4elo1]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h1, h87, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p132_1, u2elo0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h2, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h6, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p132_1, u2elo0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [h130, hlam, p132_0]
                            · have p132_0 := h132c.1
                              have p132_1 := h132c.2.1
                              have p132_2 := h132c.2.2.1
                              have p132_3 := h132c.2.2.2
                              linarith only [hlam, p132_0]
                          · linarith only [h131, h7, hc13, hlam, hphi, ht34, u4elo4]
                        · linarith only [h130, h3, hc24, hlam, hphi, u4elo0]
                  · linarith only [h3, h84, hc14, hlam, hphi, u4elo0]
              · linarith only [h2, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h196 | h196
          · rcases m.htr 1 2 4 (by decide) (by decide) with h197 | h197
            · rcases m.htr 1 2 5 (by decide) (by decide) with h198 | h198
              · rcases m.htr 1 3 4 (by decide) (by decide) with h199 | h199
                · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
                  · linarith only [h200, h3, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                        · linarith only [h1, h200, h204, hc14, hlam, hphi, u4elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                          · linarith only [h1, h202, h206, h3, hlam]
                          · rcases h2bigk with h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hc12, hlam, hphi, p208_1, u2elo0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h203, h206, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p208_1, u2elo0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              rcases p208_3 (m.d 0 2) (by simp) with h212 | h212
                              · rcases p208_3 (m.d 1 2) (by simp) with h213 | h213
                                · rcases p208_3 (m.d 2 3) (by simp) with h214 | h214
                                  · linarith only [h0, h214, hlam]
                                  · linarith only [h202, h214, hlam]
                                · linarith only [h197, h213, hlam]
                              · linarith only [h212, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              rcases p208_3 (m.d 0 2) (by simp) with h219 | h219
                              · rcases p208_3 (m.d 1 2) (by simp) with h220 | h220
                                · rcases p208_3 (m.d 2 3) (by simp) with h221 | h221
                                  · linarith only [h0, h221, hlam]
                                  · linarith only [h203, h221, hlam]
                                · linarith only [h198, h220, hlam]
                              · linarith only [h219, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hc02, hlam, hphi, p208_1, u2elo1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h203, h206, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p208_1, u2elo1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              rcases p208_3 (m.d 0 2) (by simp) with h229 | h229
                              · rcases p208_3 (m.d 1 2) (by simp) with h230 | h230
                                · rcases p208_3 (m.d 2 3) (by simp) with h231 | h231
                                  · linarith only [h196, h231, hlam]
                                  · linarith only [h202, h231, hlam]
                                · linarith only [h230, hlam, p208_0]
                              · linarith only [h1, h229, hlam]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              rcases p208_3 (m.d 0 2) (by simp) with h236 | h236
                              · rcases p208_3 (m.d 1 2) (by simp) with h237 | h237
                                · rcases p208_3 (m.d 2 3) (by simp) with h238 | h238
                                  · linarith only [h196, h238, hlam]
                                  · linarith only [h203, h238, hlam]
                                · linarith only [h237, hlam, p208_0]
                              · linarith only [h2, h236, hlam]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h0, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h196, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h0, h202, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p208_1, u2elo0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h0, h202, h204, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p208_1, u2elo0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h1, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h197, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h202, hlam, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h204, hlam, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h2, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h198, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h203, hlam, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h2, h202, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p208_1, u2elo0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hlam, p208_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                        · linarith only [h1, h258, h3, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h260 | h260
                          · linarith only [h202, h260, h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · linarith only [h202, h203, h260, hc34, hlam, hphi, u4elo4]
                    · linarith only [h199, h200, h202, hc23, hlam, hphi, ht34, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h264 | h264
                  · linarith only [h264, h3, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h266 | h266
                    · linarith only [h196, h199, h264, h266, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h268 | h268
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h269 | h269
                        · linarith only [h1, h199, h264, h269, hc13, hlam, hphi, ht34, u4elo0]
                        · linarith only [h266, h268, h269, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h272 | h272
                        · linarith only [h272, h3, hc04, hlam, hphi, u4elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h274 | h274
                          · linarith only [h196, h199, h264, h274, hc23, hlam, hphi, ht34, u4elo3]
                          · linarith only [h196, h199, h274, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h198, h2, hc12, hlam, hphi, u2elo0]
            · linarith only [h1, h196, h197, hc23, hlam, hphi, ht34, u4elo0]
          · linarith only [h0, h196, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h280 | h280
        · linarith only [h1, h2, h280, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h282 | h282
          · rcases m.htr 1 2 4 (by decide) (by decide) with h283 | h283
            · rcases m.htr 1 2 5 (by decide) (by decide) with h284 | h284
              · linarith only [h2, h284, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h286 | h286
                · rcases m.htr 1 4 5 (by decide) (by decide) with h287 | h287
                  · linarith only [h280, h287, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h289 | h289
                    · linarith only [h0, h2, h289, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h282, h284, h286, h289, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h292 | h292
                  · linarith only [h1, h280, h292, hc24, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                    · linarith only [h0, h2, h294, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h296 | h296
                      · linarith only [h0, h2, h296, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h298 | h298
                        · linarith only [h1, h2, h292, h298, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h1, h2, h294, h298, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h1, h282, h283, hc23, hlam, hphi, ht34, u4elo0]
          · linarith only [h0, h2, h282, hc12, hlam, hphi, u2elo4]
    · linarith only [h0, h1, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h304 | h304
    · rcases m.htr 0 2 5 (by decide) (by decide) with h305 | h305
      · rcases m.htr 0 4 5 (by decide) (by decide) with h306 | h306
        · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
          · linarith only [h0, h304, h307, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h309 | h309
            · rcases m.htr 1 2 5 (by decide) (by decide) with h310 | h310
              · rcases m.htr 1 3 4 (by decide) (by decide) with h311 | h311
                · rcases m.htr 1 4 5 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h313 | h313
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h314 | h314
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h315 | h315
                        · linarith only [h0, h304, h315, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · linarith only [h312, h315, hc24, hlam, hphi, u4elo1]
                      · linarith only [h0, h305, h314, hlam]
                    · linarith only [h0, h304, h306, h313, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h0, h304, h306, h312, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h307, h309, h311, hc24, hlam, hphi, u4elo3]
              · linarith only [h0, h305, h309, h310, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h304, h309, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h324 | h324
          · linarith only [h0, h324, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h326 | h326
            · rcases m.htr 1 2 5 (by decide) (by decide) with h327 | h327
              · rcases m.htr 1 3 4 (by decide) (by decide) with h328 | h328
                · rcases m.htr 1 4 5 (by decide) (by decide) with h329 | h329
                  · linarith only [h306, h329, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h331 | h331
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h332 | h332
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h333 | h333
                        · linarith only [h0, h304, h329, h333, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h335 | h335
                          · linarith only [h304, h306, h331, h335, hlam]
                          · rcases h2bigk with h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [hlam, p337_0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p337_1, u2elo2]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h0, hlam, p337_0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h0, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p337_1, u2elo2]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p337_1, u2elo2]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [hc02, hlam, hphi, p337_1, u2elo1]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [hlam, p337_0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h324, hlam, p337_0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h324, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p337_1, u2elo2]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h324, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p337_1, u2elo2]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [hc02, hlam, hphi, p337_1, u2elo2]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [hc12, hlam, hphi, p337_1, u2elo2]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [hlam, p337_0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              rcases p337_3 (m.d 0 2) (by simp) with h351 | h351
                              · linarith only [h0, h351, hlam]
                              · linarith only [h304, h351, hlam]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              rcases p337_3 (m.d 0 2) (by simp) with h354 | h354
                              · linarith only [h0, h354, hlam]
                              · linarith only [h305, h354, hlam]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h304, hlam, p337_0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h326, hlam, p337_0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h331, hlam, p337_1]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [hlam, p337_0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h333, hlam, p337_1]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h305, hlam, p337_0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h327, hlam, p337_0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h332, hlam, p337_1]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [h305, h331, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p337_1, u2elo0]
                            · have p337_0 := h337c.1
                              have p337_1 := h337c.2.1
                              have p337_2 := h337c.2.2.1
                              have p337_3 := h337c.2.2.2
                              linarith only [hlam, p337_0]
                      · linarith only [h0, h305, h332, hlam]
                    · linarith only [h0, h331, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h324, h326, h328, hc24, hlam, hphi, u4elo3]
              · linarith only [h0, h305, h326, h327, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h304, h326, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h372 | h372
        · linarith only [h304, h305, h372, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h374 | h374
          · linarith only [h0, h374, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h376 | h376
            · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
              · linarith only [h304, h305, h374, h377, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h379 | h379
                · rcases m.htr 1 4 5 (by decide) (by decide) with h380 | h380
                  · linarith only [h372, h380, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h382 | h382
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h383 | h383
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h384 | h384
                        · linarith only [h304, h380, h384, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · linarith only [h304, h305, h384, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h387 | h387
                        · linarith only [h0, h304, h383, h387, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h304, h382, h383, h387, hc34, hlam, hphi, u4elo4]
                    · linarith only [h0, h382, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h374, h376, h379, hc24, hlam, hphi, u4elo3]
            · linarith only [h0, h304, h376, hc12, hlam, hphi, u2elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h393 | h393
      · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
        · rcases m.htr 1 2 3 (by decide) (by decide) with h395 | h395
          · linarith only [h0, h395, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h397 | h397
            · linarith only [h304, h393, h395, h397, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h399 | h399
              · rcases m.htr 1 3 4 (by decide) (by decide) with h400 | h400
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
                              linarith only [h304, hc12, hlam, hphi, ht23, ht34, p406_1, u4elo2]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h0, hlam, p406_0]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h304, hlam, p406_0]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h304, h403, h405, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p406_1, u4elo2]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [hc02, hlam, hphi, p406_1, u2elo1]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [hlam, p406_0]
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
                              linarith only [h397, h403, h405, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p406_1, u4elo2]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h393, h403, h405, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p406_1, u2elo2]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [hc12, hlam, hphi, p406_1, u2elo2]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [hlam, p406_0]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h304, h393, h403, h405, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p406_1, u2elo2]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              rcases p406_3 (m.d 0 2) (by simp) with h421 | h421
                              · linarith only [h0, h421, hlam]
                              · linarith only [h393, h421, hlam]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h393, h403, h405, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p406_1, u2elo3]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h399, h403, h405, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p406_1, u4elo2]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h402, hlam, p406_1]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [hlam, p406_0]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              rcases p406_3 (m.d 0 2) (by simp) with h428 | h428
                              · linarith only [h304, h428, hlam]
                              · linarith only [h393, h428, hlam]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h393, hlam, p406_0]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h399, hlam, p406_0]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h403, hlam, p406_1]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [h404, hlam, p406_0]
                            · have p406_0 := h406c.1
                              have p406_1 := h406c.2.1
                              have p406_2 := h406c.2.2.1
                              have p406_3 := h406c.2.2.2
                              linarith only [hlam, p406_0]
                          · linarith only [h394, h405, hc34, hlam, hphi, u4elo0]
                        · linarith only [h304, h393, h394, h404, hlam]
                      · linarith only [h397, h399, h403, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h402, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h304, h393, h394, h401, hc14, hlam, hphi, u4elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h441 | h441
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h442 | h442
                    · linarith only [h395, h399, h400, h442, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h0, h442, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h0, h393, h394, h395, h400, h441, hc12, hlam, hphi, u2elo2]
              · linarith only [h304, h393, h399, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · linarith only [h304, h393, h394, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h448 | h448
        · rcases m.htr 1 2 3 (by decide) (by decide) with h449 | h449
          · linarith only [h0, h449, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
            · linarith only [h304, h449, h451, hc02, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
              · linarith only [h393, h451, h453, hc02, hlam, hphi, ht23, ht34, u4elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h455 | h455
                · rcases m.htr 1 4 5 (by decide) (by decide) with h456 | h456
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h457 | h457
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h458 | h458
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h459 | h459
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h460 | h460
                          · rcases h2bigk with h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hc12, hlam, hphi, p461_1, u2elo0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h0, hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h304, hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h393, hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hc02, hlam, hphi, p461_1, u2elo1]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h449, hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h451, hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h453, hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hc02, hlam, hphi, p461_1, u2elo2]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hc12, hlam, hphi, p461_1, u2elo2]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h304, hc02, hlam, hphi, p461_1, u2elo2]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h393, hc02, hlam, hphi, p461_1, u2elo2]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hc02, hlam, hphi, p461_1, u2elo3]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p461_1, u4elo2]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h457, hlam, p461_1]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h393, hc02, hlam, hphi, ht23, ht34, p461_1, u4elo2]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hc02, hlam, hphi, p461_1, u2elo4]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hc12, hlam, hphi, p461_1, u2elo4]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h458, hlam, p461_1]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [h459, hlam, p461_0]
                            · have p461_0 := h461c.1
                              have p461_1 := h461c.2.1
                              have p461_2 := h461c.2.2.1
                              have p461_3 := h461c.2.2.2
                              linarith only [hlam, p461_0]
                          · linarith only [h448, h460, hc34, hlam, hphi, u4elo0]
                        · linarith only [h304, h448, h459, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h489 | h489
                        · linarith only [h457, h458, h489, hlam]
                        · linarith only [h304, h456, h489, hc04, hlam, hphi, u4elo1]
                    · linarith only [h0, h457, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h448, h456, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h494 | h494
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h495 | h495
                    · linarith only [h449, h455, h495, hc12, hlam, hphi, u2elo2]
                    · linarith only [h0, h495, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h304, h448, h494, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
          · linarith only [h0, h499, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h501 | h501
            · linarith only [h304, h499, h501, hc02, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h503 | h503
              · linarith only [h393, h501, h503, hc02, hlam, hphi, ht23, ht34, u4elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h505 | h505
                · rcases m.htr 1 4 5 (by decide) (by decide) with h506 | h506
                  · linarith only [h448, h506, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h508 | h508
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h509 | h509
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h510 | h510
                        · linarith only [h501, h506, h510, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h304, h510, hc02, hlam, hphi, ht23, ht34, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h513 | h513
                        · linarith only [h304, h448, h513, hc02, hlam, hphi, u2elo3]
                        · linarith only [h304, h513, hc02, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h0, h508, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h517 | h517
                  · linarith only [h304, h448, h517, hc02, hlam, hphi, ht23, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
                    · linarith only [h499, h505, h519, hc12, hlam, hphi, u2elo2]
                    · linarith only [h0, h519, hc02, hlam, hphi, ht23, ht34, u4elo3]

end R2N4
