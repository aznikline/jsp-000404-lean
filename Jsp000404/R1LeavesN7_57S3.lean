import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3892000 in
set_option maxHeartbeats 3892000 in
theorem r1l7_20_11_13_14_H_L_L_0_L_I_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h3, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h12, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
                · linarith only [h15, h6, h7, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                  · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h17, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h20 | h20
              · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h22, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h20, h21, h6, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                  · linarith only [h0, h27, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h27, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                  · linarith only [h0, h30, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h3, h30, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
            · rcases m.htr 0 3 5 (by decide) (by decide) with h34 | h34
              · linarith only [h3, h34, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                · linarith only [h3, h33, h36, h5, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                  · linarith only [h0, h38, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h3, h38, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h41 | h41
              · linarith only [h33, h4, h41, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
                · linarith only [h4, h43, h5, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                  · linarith only [h0, h45, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h3, h45, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h48 | h48
          · rcases m.htr 0 3 4 (by decide) (by decide) with h49 | h49
            · linarith only [h3, h4, h49, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h51 | h51
              · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
                · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                  · linarith only [h0, h53, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h3, h53, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h3, h4, h51, h52, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
                · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                  · linarith only [h0, h58, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h2, h3, h4, h58, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h4, h48, h57, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h62 | h62
            · linarith only [h3, h4, h62, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h64 | h64
              · linarith only [h3, h48, h64, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
                · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                  · linarith only [h0, h67, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h2, h3, h48, h66, h67, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
                  · linarith only [h0, h70, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h3, h70, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h73 | h73
        · rcases m.htr 0 2 5 (by decide) (by decide) with h74 | h74
          · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
            · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
              · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
                · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                  · linarith only [h3, h73, h78, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                    · linarith only [h1, h78, h80, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h73, h80, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
                  · linarith only [h3, h73, h83, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                    · linarith only [h1, h83, h85, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h73, h85, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h3, h74, h76, hlam]
            · linarith only [h3, h73, h75, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
            · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
              · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
                · linarith only [h73, h74, h92, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                  · linarith only [h0, h94, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                    · linarith only [h1, h94, h96, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h1, h73, h74, h91, h96, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h99 | h99
                · linarith only [h3, h73, h91, h99, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                  · linarith only [h101, h3, h73, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                    · linarith only [h1, h101, h103, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h103, h73, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h3, h73, h90, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h107 | h107
          · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
            · rcases m.htr 0 3 5 (by decide) (by decide) with h109 | h109
              · rcases m.htr 0 4 5 (by decide) (by decide) with h110 | h110
                · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                  · linarith only [h107, h111, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                    · linarith only [h1, h107, h111, h113, h73, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                      · linarith only [h1, h111, h115, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h107, h115, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h107, h110, h73, hlam]
              · linarith only [h107, h108, h109, h73, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h120 | h120
              · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                  · linarith only [h107, h122, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                    · linarith only [h1, h107, h122, h124, h73, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                      · linarith only [h1, h122, h126, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h107, h126, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h107, h108, h121, h3, hlam]
              · linarith only [h107, h120, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
            · rcases m.htr 0 3 5 (by decide) (by decide) with h132 | h132
              · rcases m.htr 0 4 5 (by decide) (by decide) with h133 | h133
                · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
                  · linarith only [h0, h134, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                    · linarith only [h0, h133, h136, h73, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                      · linarith only [h0, h107, h138, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                        · linarith only [h1, h140, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h131, h140, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
                  · linarith only [h0, h131, h143, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                    · linarith only [h1, h143, h145, h73, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                      · linarith only [h0, h107, h133, h147, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                        · linarith only [h1, h149, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h131, h149, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h152 | h152
                · linarith only [h131, h132, h152, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
                  · linarith only [h0, h131, h154, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                    · linarith only [h1, h154, h156, h73, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h158 | h158
                      · linarith only [h0, h107, h158, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                        · linarith only [h1, h160, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h131, h160, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
              · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
                  · linarith only [h0, h163, h165, h3, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                    · linarith only [h0, h167, h73, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                      · linarith only [h0, h107, h169, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                        · linarith only [h131, h163, h171, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                          · linarith only [h171, h173, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h163, h165, h173, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h131, h163, h164, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h177 | h177
                · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                  · linarith only [h0, h178, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                    · linarith only [h0, h177, h180, h73, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                      · linarith only [h1, h107, h178, h182, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
                        · linarith only [h1, h131, h184, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
                          · linarith only [h1, h163, h186, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h188 | h188
                            · linarith only [h188, h2, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h177, h188, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                  · linarith only [h0, h191, h3, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h193 | h193
                    · linarith only [h0, h193, h73, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h195 | h195
                      · linarith only [h0, h107, h195, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                        · linarith only [h1, h197, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                          · linarith only [h1, h163, h199, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h201 | h201
                            · linarith only [h0, h131, h177, h2, h201, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h205 | h205
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                                    · linarith only [h0, h131, h177, h203, h206, h3, hc12, hc23, hlam, hphi]
                                    · linarith only [h0, h131, h205, h206, h3, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h209 | h209
                                    · linarith only [h0, h205, h209, h73, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h3bigk with h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p211_1, u0elo2]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h3, hlam, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h131, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h163, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h1, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h191, hlam, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h197, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h199, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        rcases p211_3 (m.d 0 3) (by simp) with h222 | h222
                                        · linarith only [h222, h3, hlam]
                                        · rcases p211_3 (m.d 1 3) (by simp) with h224 | h224
                                          · linarith only [h191, h224, hlam]
                                          · rcases p211_3 (m.d 2 3) (by simp) with h226 | h226
                                            · rcases p211_3 (m.d 3 4) (by simp) with h227 | h227
                                              · linarith only [h203, h227, hlam]
                                              · linarith only [h131, h227, hlam]
                                            · linarith only [h226, h3, hlam]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        rcases p211_3 (m.d 0 3) (by simp) with h231 | h231
                                        · linarith only [h231, h3, hlam]
                                        · linarith only [h1, h231, hlam]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h131, h3, hc02, hc23, hlam, hphi, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h0, h131, h209, h3, hc12, hc23, hlam, hphi, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h0, h203, h3, hc12, hc23, hlam, hphi, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h191, h203, hc12, hc23, hlam, hphi, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h203, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h209, hlam, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h0, h204, h3, hc12, hc23, hlam, hphi, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h191, h204, hc12, hc23, hlam, hphi, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h204, hlam, p211_0]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [h0, h131, h204, h3, hc12, hc23, hlam, hphi, p211_1]
                                      · have p211_0 := h211c.1
                                        have p211_1 := h211c.2.1
                                        have p211_2 := h211c.2.2.1
                                        have p211_3 := h211c.2.2.2
                                        linarith only [hlam, p211_0]
                                · linarith only [h0, h131, h203, h204, h3, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                                · linarith only [h0, h163, h203, h248, h3, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h251 | h251
                                    · rcases h3bigk with h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h191, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p252_1, u0elo2]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h3, hlam, p252_1]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h131, hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h163, hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h1, hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h191, hlam, p252_1]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h197, hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h199, hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h248, h251, hc03, hc34, hlam, hphi, p252_1]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h191, h248, h251, hc12, hc34, hlam, hphi, ht23, p252_1]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h203, hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h248, hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        rcases p252_3 (m.d 0 3) (by simp) with h268 | h268
                                        · linarith only [h268, hlam, p252_0]
                                        · rcases p252_3 (m.d 1 3) (by simp) with h270 | h270
                                          · linarith only [h197, h270, hlam]
                                          · rcases p252_3 (m.d 2 3) (by simp) with h272 | h272
                                            · linarith only [h203, h272, hlam]
                                            · linarith only [h272, h3, hlam]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        rcases p252_3 (m.d 0 3) (by simp) with h275 | h275
                                        · linarith only [h131, h275, hlam]
                                        · linarith only [h1, h275, hlam]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h0, h3, hc12, hc34, hlam, hphi, ht23, p252_1]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h1, h163, h191, hc12, hc34, hlam, hphi, ht23, p252_1]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        rcases p252_3 (m.d 0 3) (by simp) with h281 | h281
                                        · linarith only [h281, hlam, p252_0]
                                        · rcases p252_3 (m.d 1 3) (by simp) with h283 | h283
                                          · linarith only [h199, h283, hlam]
                                          · rcases p252_3 (m.d 2 3) (by simp) with h285 | h285
                                            · linarith only [h248, h285, hlam]
                                            · linarith only [h285, h3, hlam]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        rcases p252_3 (m.d 0 3) (by simp) with h288 | h288
                                        · linarith only [h163, h288, hlam]
                                        · linarith only [h1, h288, hlam]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p252_1]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [h251, hlam, p252_0]
                                      · have p252_0 := h252c.1
                                        have p252_1 := h252c.2.1
                                        have p252_2 := h252c.2.2.1
                                        have p252_3 := h252c.2.2.2
                                        linarith only [hlam, p252_0]
                                    · linarith only [h203, h250, h251, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h295 | h295
                                    · linarith only [h0, h203, h250, h295, h3, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h203, h295, h3, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h298 | h298
      · rcases m.htr 0 2 4 (by decide) (by decide) with h299 | h299
        · linarith only [h0, h2, h299, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h301 | h301
          · rcases m.htr 0 3 4 (by decide) (by decide) with h302 | h302
            · linarith only [h1, h2, h302, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h304 | h304
              · rcases m.htr 0 4 5 (by decide) (by decide) with h305 | h305
                · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
                  · linarith only [h0, h2, h306, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h298, h306, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h2, h298, h304, h305, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h310 | h310
                · rcases m.htr 1 2 3 (by decide) (by decide) with h311 | h311
                  · linarith only [h0, h2, h311, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h298, h311, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h2, h301, h310, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h315 | h315
            · linarith only [h1, h2, h315, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h317 | h317
              · linarith only [h298, h301, h317, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h319 | h319
                · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
                  · linarith only [h0, h2, h320, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h2, h298, h320, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h323 | h323
                  · linarith only [h0, h2, h319, h323, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h2, h298, h319, h323, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h326 | h326
        · linarith only [h1, h2, h298, h326, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h328 | h328
          · rcases m.htr 0 3 4 (by decide) (by decide) with h329 | h329
            · linarith only [h1, h2, h329, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h331 | h331
              · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
                · rcases m.htr 1 2 3 (by decide) (by decide) with h333 | h333
                  · linarith only [h298, h328, h333, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h335 | h335
                    · linarith only [h326, h328, h335, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h337 | h337
                      · linarith only [h1, h333, h337, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h328, h337, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1, h2, h298, h328, h332, hlam]
              · linarith only [h298, h328, h331, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h342 | h342
            · linarith only [h1, h2, h342, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h344 | h344
              · rcases m.htr 0 4 5 (by decide) (by decide) with h345 | h345
                · rcases m.htr 1 2 3 (by decide) (by decide) with h346 | h346
                  · linarith only [h0, h2, h298, h346, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h348 | h348
                    · linarith only [h0, h1, h2, h326, h348, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h350 | h350
                      · linarith only [h1, h328, h346, h350, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h352 | h352
                        · linarith only [h1, h2, h342, h344, h352, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h354 | h354
                          · linarith only [h1, h2, h354, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h344, h354, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h1, h2, h344, h345, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h358 | h358
                · rcases m.htr 1 2 3 (by decide) (by decide) with h359 | h359
                  · linarith only [h0, h2, h298, h359, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h361 | h361
                    · linarith only [h0, h2, h361, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h363 | h363
                      · linarith only [h1, h2, h328, h359, h363, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h365 | h365
                        · linarith only [h0, h1, h2, h342, h365, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h367 | h367
                          · linarith only [h1, h298, h344, h367, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h369 | h369
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h370 | h370
                              · linarith only [h0, h2, h365, h370, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h372 | h372
                                · linarith only [h0, h298, h344, h370, h372, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h374 | h374
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h375 | h375
                                    · rcases h3bigk with h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h359, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p376_1, u0elo2]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h298, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h342, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h344, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h359, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h365, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h367, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h372, h375, hc03, hc34, hlam, hphi, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h359, h372, h375, hc12, hc34, hlam, hphi, ht23, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h370, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h372, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        rcases p376_3 (m.d 0 3) (by simp) with h392 | h392
                                        · linarith only [h392, hlam, p376_0]
                                        · rcases p376_3 (m.d 1 3) (by simp) with h394 | h394
                                          · linarith only [h365, h394, hlam]
                                          · rcases p376_3 (m.d 2 3) (by simp) with h396 | h396
                                            · linarith only [h370, h396, hlam]
                                            · linarith only [h298, h396, hlam]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        rcases p376_3 (m.d 0 3) (by simp) with h399 | h399
                                        · linarith only [h342, h399, hlam]
                                        · linarith only [h1, h399, hlam]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h0, h298, hc12, hc34, hlam, hphi, ht23, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, h344, h359, hc12, hc34, hlam, hphi, ht23, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        rcases p376_3 (m.d 0 3) (by simp) with h405 | h405
                                        · linarith only [h405, hlam, p376_0]
                                        · rcases p376_3 (m.d 1 3) (by simp) with h407 | h407
                                          · linarith only [h367, h407, hlam]
                                          · rcases p376_3 (m.d 2 3) (by simp) with h409 | h409
                                            · linarith only [h372, h409, hlam]
                                            · linarith only [h298, h409, hlam]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        rcases p376_3 (m.d 0 3) (by simp) with h412 | h412
                                        · linarith only [h344, h412, hlam]
                                        · linarith only [h1, h412, hlam]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h0, h298, hc12, hc35, hlam, hphi, ht23, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h375, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                    · linarith only [h358, h375, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                  · linarith only [h1, h2, h358, h359, h361, h374, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h1, h2, h358, h359, h369, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
                  · linarith only [h0, h298, h421, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                    · linarith only [h0, h423, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h425 | h425
                      · linarith only [h0, h328, h358, h425, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                        · linarith only [h1, h2, h298, h342, h358, h427, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h429 | h429
                          · linarith only [h1, h2, h358, h429, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h431 | h431
                            · linarith only [h2, h358, h431, hc01, hlam, hphi, u1elo3]
                            · linarith only [h1, h2, h421, h431, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h434 | h434
    · rcases m.htr 0 2 3 (by decide) (by decide) with h435 | h435
      · linarith only [h0, h1, h435, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h437 | h437
        · rcases m.htr 0 2 5 (by decide) (by decide) with h438 | h438
          · rcases m.htr 0 3 4 (by decide) (by decide) with h439 | h439
            · rcases m.htr 0 3 5 (by decide) (by decide) with h440 | h440
              · rcases m.htr 0 4 5 (by decide) (by decide) with h441 | h441
                · rcases m.htr 1 2 3 (by decide) (by decide) with h442 | h442
                  · linarith only [h435, h437, h442, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h444 | h444
                    · linarith only [h0, h444, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h437, h444, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h447 | h447
                  · linarith only [h435, h437, h447, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h449 | h449
                    · linarith only [h0, h449, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h437, h449, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1, h438, h440, hlam]
            · linarith only [h1, h434, h439, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h454 | h454
            · rcases m.htr 0 3 5 (by decide) (by decide) with h455 | h455
              · rcases m.htr 0 4 5 (by decide) (by decide) with h456 | h456
                · linarith only [h437, h438, h456, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h458 | h458
                  · linarith only [h435, h437, h458, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h460 | h460
                    · linarith only [h0, h460, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h437, h460, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h463 | h463
                · linarith only [h0, h1, h437, h455, h463, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h465 | h465
                  · linarith only [h435, h437, h465, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h467 | h467
                    · linarith only [h0, h1, h455, h467, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h437, h467, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1, h437, h454, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h471 | h471
          · rcases m.htr 0 3 4 (by decide) (by decide) with h472 | h472
            · rcases m.htr 0 3 5 (by decide) (by decide) with h473 | h473
              · rcases m.htr 0 4 5 (by decide) (by decide) with h474 | h474
                · rcases m.htr 1 2 3 (by decide) (by decide) with h475 | h475
                  · linarith only [h435, h471, h475, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h477 | h477
                    · linarith only [h0, h1, h437, h471, h477, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h479 | h479
                      · linarith only [h1, h434, h477, h479, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h471, h479, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h437, h471, h474, hlam]
              · linarith only [h1, h434, h437, h471, h473, hlam]
            · linarith only [h1, h434, h472, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h485 | h485
            · rcases m.htr 0 3 5 (by decide) (by decide) with h486 | h486
              · rcases m.htr 0 4 5 (by decide) (by decide) with h487 | h487
                · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                  · linarith only [h0, h1, h435, h488, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                    · linarith only [h0, h437, h487, h490, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                      · linarith only [h1, h434, h471, h490, h492, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h496 | h496
                            · linarith only [h1, h434, h496, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h487, h496, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h1, h486, h495, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1, h434, h490, h494, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h501 | h501
                  · linarith only [h0, h1, h501, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h503 | h503
                    · linarith only [h0, h437, h503, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h505 | h505
                      · linarith only [h1, h434, h471, h503, h505, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h507 | h507
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h508 | h508
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h509 | h509
                            · linarith only [h1, h434, h487, h509, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h511 | h511
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h512 | h512
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h513 | h513
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h514 | h514
                                    · linarith only [h434, h487, h507, h514, hlam]
                                    · rcases h3bigk with h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [hlam, p516_0]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h1, hlam, p516_1]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h435, hlam, p516_1]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p516_1, u0elo2]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [hc35, hlam, hphi, ht0b, ht5b, p516_1, u0elo2]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h1, h434, h503, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p516_1, u1elo2]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [hlam, p516_0]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h501, hlam, p516_1]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        rcases p516_3 (m.d 0 3) (by simp) with h525 | h525
                                        · linarith only [h1, h525, hlam]
                                        · linarith only [h485, h525, hlam]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        rcases p516_3 (m.d 0 3) (by simp) with h528 | h528
                                        · linarith only [h1, h528, hlam]
                                        · linarith only [h486, h528, hlam]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h1, h434, h503, hc12, hc23, hlam, hphi, p516_1]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h1, h434, h503, hc12, hc23, hlam, hphi, p516_1]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [hlam, p516_0]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        rcases p516_3 (m.d 0 3) (by simp) with h534 | h534
                                        · linarith only [h435, h534, hlam]
                                        · linarith only [h485, h534, hlam]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        rcases p516_3 (m.d 0 3) (by simp) with h537 | h537
                                        · linarith only [h435, h537, hlam]
                                        · linarith only [h486, h537, hlam]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h485, hlam, p516_0]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h507, hlam, p516_0]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h511, hlam, p516_0]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [hlam, p516_0]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h514, hlam, p516_1]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h486, hlam, p516_0]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h508, hlam, p516_0]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h512, hlam, p516_0]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [h486, hc34, hlam, hphi, ht0b, ht45, ht5b, p516_1, u0elo2]
                                      · have p516_0 := h516c.1
                                        have p516_1 := h516c.2.1
                                        have p516_2 := h516c.2.2.1
                                        have p516_3 := h516c.2.2.2
                                        linarith only [hlam, p516_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h550 | h550
                                    · linarith only [h0, h437, h513, h550, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h3bigk with h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [hlam, p552_0]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h1, hlam, p552_1]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h435, hlam, p552_1]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p552_1, u0elo2]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [hc35, hlam, hphi, ht0b, ht5b, p552_1, u0elo2]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h1, hc01, hlam, hphi, p552_1, u1elo2]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [hlam, p552_0]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h501, hlam, p552_1]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        rcases p552_3 (m.d 0 3) (by simp) with h561 | h561
                                        · linarith only [h1, h561, hlam]
                                        · linarith only [h485, h561, hlam]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        rcases p552_3 (m.d 0 3) (by simp) with h564 | h564
                                        · linarith only [h1, h564, hlam]
                                        · linarith only [h486, h564, hlam]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h1, h434, h503, hc12, hc23, hlam, hphi, p552_1]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h1, h434, h503, hc12, hc23, hlam, hphi, p552_1]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [hlam, p552_0]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        rcases p552_3 (m.d 0 3) (by simp) with h570 | h570
                                        · linarith only [h435, h570, hlam]
                                        · linarith only [h485, h570, hlam]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        rcases p552_3 (m.d 0 3) (by simp) with h573 | h573
                                        · linarith only [h435, h573, hlam]
                                        · linarith only [h486, h573, hlam]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h485, hlam, p552_0]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h507, hlam, p552_0]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h511, hlam, p552_0]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [hlam, p552_0]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h550, hlam, p552_1]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h486, hlam, p552_0]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h508, hlam, p552_0]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h512, hlam, p552_0]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [h486, hc34, hlam, hphi, ht0b, ht45, ht5b, p552_1, u0elo2]
                                      · have p552_0 := h552c.1
                                        have p552_1 := h552c.2.1
                                        have p552_2 := h552c.2.2.1
                                        have p552_3 := h552c.2.2.2
                                        linarith only [hlam, p552_0]
                                · linarith only [h0, h435, h486, h512, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                              · linarith only [h1, h434, h501, h503, h511, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h434, h486, h503, h508, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1, h434, h503, h507, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h590 | h590
                · linarith only [h1, h434, h486, h590, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h592 | h592
                  · linarith only [h0, h592, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h594 | h594
                    · linarith only [h0, h1, h437, h486, h594, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h596 | h596
                      · linarith only [h0, h1, h434, h471, h486, h596, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h598 | h598
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h599 | h599
                          · linarith only [h1, h434, h486, h594, h599, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · linarith only [h1, h434, h594, h599, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h434, h594, h598, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h434, h485, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h604 | h604
      · linarith only [h0, h1, h604, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h606 | h606
        · linarith only [h0, h434, h606, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h608 | h608
          · rcases m.htr 0 3 4 (by decide) (by decide) with h609 | h609
            · rcases m.htr 0 3 5 (by decide) (by decide) with h610 | h610
              · rcases m.htr 0 4 5 (by decide) (by decide) with h611 | h611
                · rcases m.htr 1 2 3 (by decide) (by decide) with h612 | h612
                  · linarith only [h604, h608, h612, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h614 | h614
                    · linarith only [h0, h434, h606, h608, h609, h614, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h616 | h616
                      · linarith only [h0, h434, h609, h616, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h608, h616, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h434, h608, h611, hlam]
              · linarith only [h0, h434, h608, h609, h610, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h621 | h621
              · rcases m.htr 0 4 5 (by decide) (by decide) with h622 | h622
                · rcases m.htr 1 2 3 (by decide) (by decide) with h623 | h623
                  · linarith only [h604, h608, h623, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h625 | h625
                    · linarith only [h0, h606, h608, h625, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h627 | h627
                      · linarith only [h0, h1, h609, h627, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · linarith only [h608, h627, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h1, h608, h609, h622, hlam]
              · linarith only [h0, h1, h608, h621, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h632 | h632
            · rcases m.htr 0 3 5 (by decide) (by decide) with h633 | h633
              · rcases m.htr 0 4 5 (by decide) (by decide) with h634 | h634
                · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
                  · linarith only [h0, h604, h635, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h637 | h637
                    · linarith only [h0, h434, h606, h637, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h639 | h639
                      · linarith only [h0, h434, h608, h632, h639, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h641 | h641
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h642 | h642
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h643 | h643
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h644 | h644
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h645 | h645
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h646 | h646
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h647 | h647
                                    · linarith only [h632, h647, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                    · linarith only [h632, h634, h647, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · linarith only [h434, h632, h634, h637, h646, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h0, h434, h635, h641, h642, h645, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                              · linarith only [h0, h434, h635, h641, h644, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h434, h632, h634, h643, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h434, h633, h641, h642, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h632, h641, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h656 | h656
                  · linarith only [h0, h604, h656, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h658 | h658
                    · linarith only [h0, h434, h633, h634, h658, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
                      · linarith only [h0, h434, h633, h634, h660, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h662 | h662
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h663 | h663
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h664 | h664
                            · linarith only [h434, h634, h662, h664, hc01, hlam, hphi, u1elo2]
                            · linarith only [h0, h434, h664, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h633, h663, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1, h662, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h669 | h669
                · linarith only [h632, h633, h669, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h671 | h671
                  · linarith only [h0, h671, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h673 | h673
                    · linarith only [h0, h673, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h675 | h675
                      · linarith only [h0, h434, h608, h632, h633, h675, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h677 | h677
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                          · linarith only [h0, h434, h632, h633, h678, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · linarith only [h0, h1, h678, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h632, h677, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h682 | h682
              · rcases m.htr 0 4 5 (by decide) (by decide) with h683 | h683
                · rcases m.htr 1 2 3 (by decide) (by decide) with h684 | h684
                  · linarith only [h0, h1, h604, h684, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h686 | h686
                    · linarith only [h0, h686, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h688 | h688
                      · linarith only [h0, h608, h688, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h690 | h690
                        · linarith only [h1, h632, h690, hc01, hlam, hphi, u1elo2]
                        · linarith only [h0, h1, h690, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h632, h682, h683, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h694 | h694
                · rcases m.htr 1 2 3 (by decide) (by decide) with h695 | h695
                  · linarith only [h0, h695, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h697 | h697
                    · linarith only [h0, h697, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h699 | h699
                      · linarith only [h0, h1, h608, h682, h699, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h701 | h701
                        · linarith only [h0, h1, h632, h701, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · linarith only [h0, h1, h701, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h704 | h704
                  · linarith only [h0, h704, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h706 | h706
                    · linarith only [h0, h706, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h708 | h708
                      · linarith only [h0, h1, h608, h632, h694, h708, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h710 | h710
                        · linarith only [h1, h632, h710, hc01, hlam, hphi, u1elo2]
                        · linarith only [h0, h1, h710, hc12, hc34, hlam, hphi, ht23]

end R2N4
