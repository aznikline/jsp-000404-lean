import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sBT2_H_I_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5elo := hb5.1
  have h2elo := hb2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · linarith only [h7, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h5, hlam]
                · linarith only [h10, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h9, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · linarith only [h14, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h16 | h16
              · rcases m.htr 0 1 3 (by decide) (by decide) with h17 | h17
                · linarith only [h17, h5, hlam]
                · linarith only [h16, h17, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h16, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · linarith only [h22, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                · rcases m.htr 0 1 4 (by decide) (by decide) with h26 | h26
                  · linarith only [h21, h26, hlam]
                  · linarith only [h24, h26, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h24, h25, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h24, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h31 | h31
            · linarith only [h31, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 1 3 (by decide) (by decide) with h34 | h34
                · rcases m.htr 0 1 4 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h37 | h37
                      · linarith only [h37, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h37, h5, hlam]
                    · linarith only [h36, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h33, h35, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h33, h34, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h33, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h45 | h45
    · rcases p0_3 (m.d 0 2) (by simp) with h46 | h46
      · linarith only [h46, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h48 | h48
        · linarith only [h48, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h50 | h50
          · rcases p0_3 (m.d 0 5) (by simp) with h51 | h51
            · linarith only [h46, h51, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h53 | h53
              · rcases m.htr 0 1 3 (by decide) (by decide) with h54 | h54
                · rcases m.htr 0 1 4 (by decide) (by decide) with h55 | h55
                  · linarith only [h50, h55, hlam]
                  · linarith only [h46, h53, h55, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h54, hlam, p0_0]
              · linarith only [h46, h53, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h60 | h60
            · linarith only [h46, h60, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
              · rcases m.htr 0 1 3 (by decide) (by decide) with h63 | h63
                · rcases m.htr 0 1 4 (by decide) (by decide) with h64 | h64
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h65 | h65
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h66 | h66
                      · linarith only [h46, h66, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h68 | h68
                        · linarith only [h66, h68, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h70 | h70
                          · linarith only [h66, h70, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                          · linarith only [h70, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h65, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h46, h62, h64, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h63, hlam, p0_0]
              · linarith only [h46, h62, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h45, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h78 | h78
    · rcases p0_3 (m.d 0 2) (by simp) with h79 | h79
      · linarith only [h79, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h81 | h81
        · rcases p0_3 (m.d 0 4) (by simp) with h82 | h82
          · linarith only [h82, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h84 | h84
            · linarith only [h79, h84, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h86 | h86
              · rcases m.htr 0 1 3 (by decide) (by decide) with h87 | h87
                · linarith only [h81, h87, hlam]
                · linarith only [h79, h86, h87, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h79, h86, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h93 | h93
            · linarith only [h79, h93, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h95 | h95
              · rcases m.htr 0 1 3 (by decide) (by decide) with h96 | h96
                · rcases m.htr 0 1 4 (by decide) (by decide) with h97 | h97
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h99 | h99
                      · linarith only [h79, h99, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h101 | h101
                        · linarith only [h101, h79, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h103 | h103
                          · linarith only [h103, h81, h99, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                          · linarith only [h103, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h81, h98, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h97, hlam, p0_0]
                · linarith only [h79, h95, h96, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h79, h95, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h78, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h111 | h111
    · rcases p0_3 (m.d 0 2) (by simp) with h112 | h112
      · linarith only [h112, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h114 | h114
        · rcases p0_3 (m.d 0 4) (by simp) with h115 | h115
          · rcases p0_3 (m.d 0 5) (by simp) with h116 | h116
            · linarith only [h116, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
              · rcases m.htr 0 1 3 (by decide) (by decide) with h119 | h119
                · linarith only [h114, h119, hlam]
                · linarith only [h112, h118, h119, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h118, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h123 | h123
            · linarith only [h123, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h125 | h125
              · rcases m.htr 0 1 3 (by decide) (by decide) with h126 | h126
                · linarith only [h114, h126, hlam]
                · linarith only [h112, h125, h126, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h125, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h130 | h130
          · rcases p0_3 (m.d 0 5) (by simp) with h131 | h131
            · linarith only [h131, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h133 | h133
              · rcases m.htr 0 1 3 (by decide) (by decide) with h134 | h134
                · rcases m.htr 0 1 4 (by decide) (by decide) with h135 | h135
                  · linarith only [h130, h135, hlam]
                  · linarith only [h112, h133, h135, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h112, h133, h134, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h133, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h140 | h140
            · linarith only [h140, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h142 | h142
              · rcases m.htr 0 1 3 (by decide) (by decide) with h143 | h143
                · rcases m.htr 0 1 4 (by decide) (by decide) with h144 | h144
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h145 | h145
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h146 | h146
                      · linarith only [h112, h146, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h148 | h148
                        · linarith only [h114, h146, h148, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h150 | h150
                          · linarith only [h112, h150, hlam]
                          · linarith only [h150, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h145, hlam, p0_0]
                  · linarith only [h114, h144, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h112, h142, h143, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h142, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h111, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, p0_1, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h163 | h163
    · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h165 | h165
      · linarith only [h165, hc01, hlam, hphi, ht12, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h167 | h167
        · rcases p0_3 (m.d 0 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 0 5) (by simp) with h169 | h169
            · linarith only [h169, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h171 | h171
              · linarith only [h171, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h165, h171, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h174 | h174
            · linarith only [h174, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h176 | h176
              · linarith only [h176, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h165, h176, hlam]
        · linarith only [h167, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h180 | h180
    · rcases p0_3 (m.d 0 2) (by simp) with h181 | h181
      · linarith only [h181, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h183 | h183
        · rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
          · rcases p0_3 (m.d 0 5) (by simp) with h185 | h185
            · linarith only [h185, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h187 | h187
              · rcases m.htr 0 1 3 (by decide) (by decide) with h188 | h188
                · rcases m.htr 0 1 4 (by decide) (by decide) with h189 | h189
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h190 | h190
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h191 | h191
                      · linarith only [h191, hlam, p0_0]
                      · linarith only [h187, h191, hc12, hlam, hphi, p0_1, u2elo2]
                    · linarith only [h187, h188, h190, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h187, h188, h189, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h180, h188, hlam]
              · linarith only [h180, h187, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h198 | h198
            · linarith only [h198, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h200 | h200
              · rcases m.htr 0 1 3 (by decide) (by decide) with h201 | h201
                · rcases m.htr 0 1 4 (by decide) (by decide) with h202 | h202
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h203 | h203
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h204 | h204
                      · linarith only [h204, hlam, p0_0]
                      · linarith only [h200, h204, hc12, hlam, hphi, p0_1, u2elo2]
                    · linarith only [h200, h201, h203, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h200, h201, h202, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h180, h201, hlam]
              · linarith only [h180, h200, hc02, hlam, hphi, p0_1, u2elo1]
        · linarith only [h183, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h212 | h212
      · linarith only [h212, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h214 | h214
        · rcases p0_3 (m.d 0 4) (by simp) with h215 | h215
          · rcases p0_3 (m.d 0 5) (by simp) with h216 | h216
            · linarith only [h180, h216, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h218 | h218
              · linarith only [h180, h218, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h220 | h220
                · linarith only [h218, h220, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h218, h220, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h223 | h223
            · linarith only [h223, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h225 | h225
              · linarith only [h180, h225, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h227 | h227
                · linarith only [h225, h227, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h225, h227, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h214, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h232 | h232
    · rcases p0_3 (m.d 0 2) (by simp) with h233 | h233
      · linarith only [h233, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h235 | h235
        · rcases p0_3 (m.d 0 4) (by simp) with h236 | h236
          · linarith only [h236, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h238 | h238
            · linarith only [h233, h238, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h240 | h240
              · rcases m.htr 0 1 3 (by decide) (by decide) with h241 | h241
                · rcases m.htr 0 1 4 (by decide) (by decide) with h242 | h242
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h243 | h243
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h244 | h244
                      · linarith only [h233, h241, h244, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h233, h244, hc02, hlam, hphi, p0_1, u2elo2]
                    · linarith only [h233, h240, h241, h243, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h233, h240, h241, h242, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h232, h241, hlam]
              · linarith only [h232, h233, h240, hc02, hlam, hphi, p0_1, u2elo1]
        · linarith only [h235, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h252 | h252
      · linarith only [h232, h252, hc01, hlam, hphi, ht12, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h254 | h254
        · rcases p0_3 (m.d 0 4) (by simp) with h255 | h255
          · linarith only [h255, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h257 | h257
            · linarith only [h232, h257, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h259 | h259
              · linarith only [h232, h259, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h261 | h261
                · linarith only [h232, h261, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h252, h259, h261, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h254, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h265 | h265
    · rcases p0_3 (m.d 0 2) (by simp) with h266 | h266
      · linarith only [h266, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h268 | h268
        · rcases p0_3 (m.d 0 4) (by simp) with h269 | h269
          · rcases p0_3 (m.d 0 5) (by simp) with h270 | h270
            · linarith only [h270, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h272 | h272
              · rcases m.htr 0 1 3 (by decide) (by decide) with h273 | h273
                · rcases m.htr 0 1 4 (by decide) (by decide) with h274 | h274
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h275 | h275
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h276 | h276
                      · linarith only [h266, h273, h276, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h266, h276, hc02, hlam, hphi, p0_1, u2elo2]
                    · linarith only [h266, h272, h273, h275, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h266, h272, h273, h274, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h265, h273, hlam]
              · linarith only [h265, h266, h272, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h283 | h283
            · linarith only [h283, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h285 | h285
              · rcases m.htr 0 1 3 (by decide) (by decide) with h286 | h286
                · rcases m.htr 0 1 4 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h288 | h288
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h289 | h289
                      · linarith only [h266, h286, h289, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h266, h289, hc02, hlam, hphi, p0_1, u2elo2]
                    · linarith only [h266, h285, h286, h288, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h266, h285, h286, h287, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h265, h286, hlam]
              · linarith only [h265, h266, h285, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
        · linarith only [h268, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h297 | h297
      · linarith only [h265, h297, hc01, hlam, hphi, ht12, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h299 | h299
        · rcases p0_3 (m.d 0 4) (by simp) with h300 | h300
          · rcases p0_3 (m.d 0 5) (by simp) with h301 | h301
            · linarith only [h301, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h303 | h303
              · linarith only [h265, h303, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h305 | h305
                · linarith only [h265, h305, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h297, h303, h305, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h308 | h308
            · linarith only [h308, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h310 | h310
              · linarith only [h265, h310, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h312 | h312
                · linarith only [h297, h310, h312, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h297, h310, h312, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h299, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h316 | h316
    · linarith only [h316, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h318 | h318
      · linarith only [h318, hc01, hlam, hphi, ht12, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h320 | h320
        · rcases p0_3 (m.d 0 4) (by simp) with h321 | h321
          · rcases p0_3 (m.d 0 5) (by simp) with h322 | h322
            · linarith only [h322, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h324 | h324
              · linarith only [h324, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h318, h324, hlam]
          · linarith only [h321, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h328 | h328
          · rcases p0_3 (m.d 0 5) (by simp) with h329 | h329
            · linarith only [h329, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h331 | h331
              · linarith only [h331, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h318, h331, hlam]
          · linarith only [h328, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h335 | h335
    · rcases p0_3 (m.d 0 2) (by simp) with h336 | h336
      · linarith only [h336, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h338 | h338
        · rcases p0_3 (m.d 0 4) (by simp) with h339 | h339
          · rcases p0_3 (m.d 0 5) (by simp) with h340 | h340
            · linarith only [h340, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h342 | h342
              · rcases m.htr 0 1 3 (by decide) (by decide) with h343 | h343
                · rcases m.htr 0 1 4 (by decide) (by decide) with h344 | h344
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h345 | h345
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h346 | h346
                      · linarith only [h338, h343, h346, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h338, h346, hc02, hlam, hphi, p0_1, u2elo2]
                    · linarith only [h338, h342, h343, h345, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h335, h344, hlam]
                · linarith only [h335, h342, h343, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h335, h342, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h339, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h354 | h354
          · rcases p0_3 (m.d 0 5) (by simp) with h355 | h355
            · linarith only [h355, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h357 | h357
              · rcases m.htr 0 1 3 (by decide) (by decide) with h358 | h358
                · rcases m.htr 0 1 4 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h360 | h360
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h361 | h361
                      · linarith only [h359, h361, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h338, h361, hlam]
                    · linarith only [h360, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h335, h359, hlam]
                · linarith only [h335, h357, h358, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h335, h357, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h354, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h369 | h369
      · linarith only [h369, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h371 | h371
        · rcases p0_3 (m.d 0 4) (by simp) with h372 | h372
          · rcases p0_3 (m.d 0 5) (by simp) with h373 | h373
            · linarith only [h335, h373, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h375 | h375
              · linarith only [h335, h375, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h377 | h377
                · linarith only [h371, h375, h377, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h371, h375, h377, hc01, hc13, hlam, hphi, p0_1]
          · linarith only [h372, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h381 | h381
          · rcases p0_3 (m.d 0 5) (by simp) with h382 | h382
            · linarith only [h335, h382, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h384 | h384
              · linarith only [h335, h384, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h386 | h386
                · linarith only [h384, h386, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h388 | h388
                  · linarith only [h384, h388, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h384, h388, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h381, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h392 | h392
    · rcases p0_3 (m.d 0 2) (by simp) with h393 | h393
      · linarith only [h393, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h395 | h395
        · linarith only [h395, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h397 | h397
          · rcases p0_3 (m.d 0 5) (by simp) with h398 | h398
            · linarith only [h393, h398, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h400 | h400
              · rcases m.htr 0 1 3 (by decide) (by decide) with h401 | h401
                · rcases m.htr 0 1 4 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h403 | h403
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h404 | h404
                      · linarith only [h393, h404, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h406 | h406
                        · linarith only [h402, h404, h406, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h404, h406, hc02, hlam, hphi, p0_1, u2elo3]
                    · linarith only [h393, h400, h402, h403, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h392, h402, hlam]
                · linarith only [h392, h393, h400, h401, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h392, h393, h400, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h397, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h414 | h414
      · linarith only [h392, h414, hc01, hlam, hphi, ht12, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h416 | h416
        · linarith only [h416, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h418 | h418
          · rcases p0_3 (m.d 0 5) (by simp) with h419 | h419
            · linarith only [h392, h419, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h421 | h421
              · linarith only [h392, h421, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h423 | h423
                · linarith only [h392, h423, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h425 | h425
                  · linarith only [h423, h425, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h423, h425, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h418, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h430 | h430
    · rcases p0_3 (m.d 0 2) (by simp) with h431 | h431
      · linarith only [h431, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h433 | h433
        · rcases p0_3 (m.d 0 4) (by simp) with h434 | h434
          · rcases p0_3 (m.d 0 5) (by simp) with h435 | h435
            · linarith only [h435, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h437 | h437
              · rcases m.htr 0 1 3 (by decide) (by decide) with h438 | h438
                · rcases m.htr 0 1 4 (by decide) (by decide) with h439 | h439
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h440 | h440
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h441 | h441
                      · linarith only [h431, h433, h438, h441, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h431, h433, h441, hc02, hlam, hphi, p0_1, u2elo2]
                    · linarith only [h431, h433, h437, h438, h440, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h430, h439, hlam]
                · linarith only [h430, h431, h437, h438, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h430, h431, h437, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h434, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h449 | h449
          · rcases p0_3 (m.d 0 5) (by simp) with h450 | h450
            · linarith only [h450, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h452 | h452
              · rcases m.htr 0 1 3 (by decide) (by decide) with h453 | h453
                · rcases m.htr 0 1 4 (by decide) (by decide) with h454 | h454
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h455 | h455
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h456 | h456
                      · linarith only [h431, h454, h456, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h458 | h458
                        · linarith only [h433, h454, h456, h458, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h433, h456, h458, hc02, hlam, hphi, p0_1, u2elo3]
                    · linarith only [h431, h452, h454, h455, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h430, h454, hlam]
                · linarith only [h430, h431, h452, h453, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h430, h431, h452, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h449, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h466 | h466
      · linarith only [h430, h466, hc01, hlam, hphi, ht12, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h468 | h468
        · rcases p0_3 (m.d 0 4) (by simp) with h469 | h469
          · rcases p0_3 (m.d 0 5) (by simp) with h470 | h470
            · linarith only [h470, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h472 | h472
              · linarith only [h430, h468, h472, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h474 | h474
                · linarith only [h430, h468, h474, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h466, h468, h472, h474, hc01, hc13, hlam, hphi, p0_1]
          · linarith only [h469, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h478 | h478
          · rcases p0_3 (m.d 0 5) (by simp) with h479 | h479
            · linarith only [h479, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h481 | h481
              · linarith only [h430, h481, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h483 | h483
                · linarith only [h466, h481, h483, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h485 | h485
                  · linarith only [h466, h481, h485, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h466, h481, h485, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h478, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_I_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h2ehi := hb2.1
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo2]

theorem n7l_sBT2_H_I_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have h2ehi := hb2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h3 | h3
    · rcases p0_3 (m.d 0 2) (by simp) with h4 | h4
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · linarith only [h5, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · linarith only [h4, h9, hlam]
              · linarith only [h9, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h8, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h13 | h13
            · rcases m.htr 0 1 2 (by decide) (by decide) with h14 | h14
              · linarith only [h14, h4, hlam]
              · linarith only [h14, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h13, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · linarith only [h3, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · rcases p0_3 (m.d 0 2) (by simp) with h21 | h21
      · rcases p0_3 (m.d 0 3) (by simp) with h22 | h22
        · rcases p0_3 (m.d 0 4) (by simp) with h23 | h23
          · linarith only [h23, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h25 | h25
            · rcases m.htr 0 1 2 (by decide) (by decide) with h26 | h26
              · linarith only [h21, h26, hlam]
              · linarith only [h26, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h25, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h30 | h30
          · linarith only [h30, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h32 | h32
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · linarith only [h21, h33, hlam]
              · linarith only [h22, h33, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h32, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h21, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · linarith only [h20, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h42 | h42
      · rcases p0_3 (m.d 0 3) (by simp) with h43 | h43
        · rcases p0_3 (m.d 0 4) (by simp) with h44 | h44
          · rcases p0_3 (m.d 0 5) (by simp) with h45 | h45
            · rcases m.htr 0 1 2 (by decide) (by decide) with h46 | h46
              · linarith only [h46, hlam, p0_0]
              · linarith only [h46, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h45, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h50 | h50
            · rcases m.htr 0 1 2 (by decide) (by decide) with h51 | h51
              · linarith only [h51, hlam, p0_0]
              · linarith only [h51, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h50, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h55 | h55
          · rcases p0_3 (m.d 0 5) (by simp) with h56 | h56
            · rcases m.htr 0 1 2 (by decide) (by decide) with h57 | h57
              · linarith only [h57, hlam, p0_0]
              · linarith only [h57, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h56, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h61 | h61
            · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
              · linarith only [h62, hlam, p0_0]
              · linarith only [h62, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h61, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h68 | h68
    · rcases p0_3 (m.d 0 2) (by simp) with h69 | h69
      · rcases p0_3 (m.d 0 3) (by simp) with h70 | h70
        · linarith only [h70, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 0 5) (by simp) with h73 | h73
            · rcases m.htr 0 1 2 (by decide) (by decide) with h74 | h74
              · rcases m.htr 0 1 3 (by decide) (by decide) with h75 | h75
                · rcases m.htr 0 1 4 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h78 | h78
                      · linarith only [h74, h78, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h78, hlam, p0_0]
                    · linarith only [h74, h77, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h74, h75, h76, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h74, h75, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h68, h74, hlam]
            · linarith only [h73, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h86 | h86
            · rcases m.htr 0 1 2 (by decide) (by decide) with h87 | h87
              · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
                · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h91 | h91
                      · linarith only [h87, h91, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h91, hlam, p0_0]
                    · linarith only [h87, h90, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h87, h88, h89, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h87, h88, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h68, h87, hlam]
            · linarith only [h68, h86, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h69, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h100 | h100
      · rcases p0_3 (m.d 0 3) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
            · rcases m.htr 0 1 2 (by decide) (by decide) with h105 | h105
              · linarith only [h105, h68, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h105, h68, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h104, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h109 | h109
            · rcases m.htr 0 1 2 (by decide) (by decide) with h110 | h110
              · linarith only [h110, h68, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h110, h68, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h109, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h115 | h115
    · rcases p0_3 (m.d 0 2) (by simp) with h116 | h116
      · rcases p0_3 (m.d 0 3) (by simp) with h117 | h117
        · rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
          · linarith only [h118, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h120 | h120
            · rcases m.htr 0 1 2 (by decide) (by decide) with h121 | h121
              · rcases m.htr 0 1 3 (by decide) (by decide) with h122 | h122
                · rcases m.htr 0 1 4 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h125 | h125
                      · linarith only [h117, h125, hlam]
                      · linarith only [h125, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h121, h123, h124, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h121, h123, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h121, h122, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h115, h121, hlam]
            · linarith only [h120, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
          · linarith only [h133, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h135 | h135
            · rcases m.htr 0 1 2 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 1 3 (by decide) (by decide) with h137 | h137
                · rcases m.htr 0 1 4 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h140 | h140
                      · linarith only [h117, h136, h140, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h117, h140, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h117, h136, h137, h139, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h117, h136, h137, h138, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h117, h136, h137, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h115, h136, hlam]
            · linarith only [h135, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h116, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h149 | h149
      · rcases p0_3 (m.d 0 3) (by simp) with h150 | h150
        · rcases p0_3 (m.d 0 4) (by simp) with h151 | h151
          · linarith only [h151, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h153 | h153
            · rcases m.htr 0 1 2 (by decide) (by decide) with h154 | h154
              · linarith only [h115, h154, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h115, h154, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h153, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h158 | h158
          · linarith only [h158, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h160 | h160
            · rcases m.htr 0 1 2 (by decide) (by decide) with h161 | h161
              · linarith only [h115, h161, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h115, h161, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h160, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h149, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h167 | h167
    · linarith only [h167, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h169 | h169
      · rcases p0_3 (m.d 0 3) (by simp) with h170 | h170
        · rcases p0_3 (m.d 0 4) (by simp) with h171 | h171
          · rcases p0_3 (m.d 0 5) (by simp) with h172 | h172
            · rcases m.htr 0 1 2 (by decide) (by decide) with h173 | h173
              · linarith only [h173, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h169, h173, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h169, h172, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h177 | h177
            · rcases m.htr 0 1 2 (by decide) (by decide) with h178 | h178
              · linarith only [h169, h178, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h169, h178, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h169, h177, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h170, hlam, p0_0]
      · linarith only [h169, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h186 | h186
    · rcases p0_3 (m.d 0 2) (by simp) with h187 | h187
      · rcases p0_3 (m.d 0 3) (by simp) with h188 | h188
        · rcases p0_3 (m.d 0 4) (by simp) with h189 | h189
          · linarith only [h189, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h191 | h191
            · rcases m.htr 0 1 2 (by decide) (by decide) with h192 | h192
              · rcases m.htr 0 1 3 (by decide) (by decide) with h193 | h193
                · rcases m.htr 0 1 4 (by decide) (by decide) with h194 | h194
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h195 | h195
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h196 | h196
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h197 | h197
                        · linarith only [h192, h196, h197, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
                        · linarith only [h196, h197, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h187, h196, hlam]
                    · linarith only [h193, h194, h195, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h193, h194, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h186, h193, hlam]
              · linarith only [h186, h192, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h186, h191, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h188, hlam, p0_0]
      · linarith only [h186, h187, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h208 | h208
      · rcases p0_3 (m.d 0 3) (by simp) with h209 | h209
        · rcases p0_3 (m.d 0 4) (by simp) with h210 | h210
          · linarith only [h210, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h212 | h212
            · rcases m.htr 0 1 2 (by decide) (by decide) with h213 | h213
              · linarith only [h186, h208, h213, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h186, h208, h213, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h208, h212, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h209, hlam, p0_0]
      · linarith only [h208, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h220 | h220
    · linarith only [h220, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h222 | h222
      · rcases p0_3 (m.d 0 3) (by simp) with h223 | h223
        · rcases p0_3 (m.d 0 4) (by simp) with h224 | h224
          · rcases p0_3 (m.d 0 5) (by simp) with h225 | h225
            · rcases m.htr 0 1 2 (by decide) (by decide) with h226 | h226
              · linarith only [h222, h226, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h222, h226, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h222, h225, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h224, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 0 5) (by simp) with h232 | h232
            · rcases m.htr 0 1 2 (by decide) (by decide) with h233 | h233
              · linarith only [h222, h233, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h222, h233, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h222, h232, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h231, hlam, p0_0]
      · linarith only [h222, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h240 | h240
    · rcases p0_3 (m.d 0 2) (by simp) with h241 | h241
      · rcases p0_3 (m.d 0 3) (by simp) with h242 | h242
        · linarith only [h242, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h244 | h244
          · rcases p0_3 (m.d 0 5) (by simp) with h245 | h245
            · rcases m.htr 0 1 2 (by decide) (by decide) with h246 | h246
              · rcases m.htr 0 1 3 (by decide) (by decide) with h247 | h247
                · rcases m.htr 0 1 4 (by decide) (by decide) with h248 | h248
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h249 | h249
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h250 | h250
                      · linarith only [h241, h246, h250, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h241, h250, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h241, h246, h247, h249, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h240, h248, hlam]
                · linarith only [h241, h246, h247, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h240, h246, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h240, h245, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h244, hlam, p0_0]
      · linarith only [h240, h241, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h260 | h260
      · rcases p0_3 (m.d 0 3) (by simp) with h261 | h261
        · linarith only [h261, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 0 5) (by simp) with h264 | h264
            · rcases m.htr 0 1 2 (by decide) (by decide) with h265 | h265
              · linarith only [h240, h265, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h240, h260, h265, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h260, h264, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h263, hlam, p0_0]
      · linarith only [h260, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h273 | h273
    · linarith only [h273, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h275 | h275
      · rcases p0_3 (m.d 0 3) (by simp) with h276 | h276
        · rcases p0_3 (m.d 0 4) (by simp) with h277 | h277
          · rcases p0_3 (m.d 0 5) (by simp) with h278 | h278
            · rcases m.htr 0 1 2 (by decide) (by decide) with h279 | h279
              · linarith only [h275, h279, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h275, h279, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h278, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h283 | h283
            · rcases m.htr 0 1 2 (by decide) (by decide) with h284 | h284
              · linarith only [h275, h284, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h275, h284, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h283, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h288 | h288
          · rcases p0_3 (m.d 0 5) (by simp) with h289 | h289
            · rcases m.htr 0 1 2 (by decide) (by decide) with h290 | h290
              · linarith only [h275, h290, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h275, h290, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h289, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h294 | h294
            · rcases m.htr 0 1 2 (by decide) (by decide) with h295 | h295
              · linarith only [h275, h295, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h275, h295, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h294, hlam, p0_0]
      · linarith only [h275, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h301 | h301
    · rcases p0_3 (m.d 0 2) (by simp) with h302 | h302
      · rcases p0_3 (m.d 0 3) (by simp) with h303 | h303
        · linarith only [h303, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h305 | h305
          · rcases p0_3 (m.d 0 5) (by simp) with h306 | h306
            · rcases m.htr 0 1 2 (by decide) (by decide) with h307 | h307
              · rcases m.htr 0 1 3 (by decide) (by decide) with h308 | h308
                · rcases m.htr 0 1 4 (by decide) (by decide) with h309 | h309
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h310 | h310
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h311 | h311
                      · linarith only [h302, h307, h311, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h302, h311, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h301, h310, hlam]
                  · linarith only [h302, h307, h308, h309, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h302, h307, h308, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h301, h307, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h306, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h319 | h319
            · rcases m.htr 0 1 2 (by decide) (by decide) with h320 | h320
              · rcases m.htr 0 1 3 (by decide) (by decide) with h321 | h321
                · rcases m.htr 0 1 4 (by decide) (by decide) with h322 | h322
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h323 | h323
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h324 | h324
                      · linarith only [h302, h320, h324, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h302, h324, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h301, h323, hlam]
                  · linarith only [h302, h320, h321, h322, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h302, h320, h321, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h301, h320, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h319, hlam, p0_0]
      · linarith only [h301, h302, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h333 | h333
      · rcases p0_3 (m.d 0 3) (by simp) with h334 | h334
        · linarith only [h334, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h336 | h336
          · rcases p0_3 (m.d 0 5) (by simp) with h337 | h337
            · rcases m.htr 0 1 2 (by decide) (by decide) with h338 | h338
              · linarith only [h301, h338, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h301, h333, h338, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h337, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h342 | h342
            · rcases m.htr 0 1 2 (by decide) (by decide) with h343 | h343
              · linarith only [h301, h333, h343, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h301, h333, h343, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h342, hlam, p0_0]
      · linarith only [h333, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h348 | h348
    · rcases p0_3 (m.d 0 2) (by simp) with h349 | h349
      · rcases p0_3 (m.d 0 3) (by simp) with h350 | h350
        · rcases p0_3 (m.d 0 4) (by simp) with h351 | h351
          · linarith only [h351, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h353 | h353
            · rcases m.htr 0 1 2 (by decide) (by decide) with h354 | h354
              · rcases m.htr 0 1 3 (by decide) (by decide) with h355 | h355
                · rcases m.htr 0 1 4 (by decide) (by decide) with h356 | h356
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h357 | h357
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h358 | h358
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h359 | h359
                        · linarith only [h350, h354, h358, h359, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
                        · linarith only [h350, h358, h359, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h349, h356, h358, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h348, h357, hlam]
                  · linarith only [h348, h356, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h349, h354, h355, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h348, h354, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h353, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h368 | h368
          · linarith only [h368, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h370 | h370
            · rcases m.htr 0 1 2 (by decide) (by decide) with h371 | h371
              · rcases m.htr 0 1 3 (by decide) (by decide) with h372 | h372
                · rcases m.htr 0 1 4 (by decide) (by decide) with h373 | h373
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h374 | h374
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h375 | h375
                      · linarith only [h349, h350, h371, h375, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h349, h350, h375, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h348, h374, hlam]
                  · linarith only [h349, h350, h371, h372, h373, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h349, h350, h371, h372, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h348, h350, h371, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h370, hlam, p0_0]
      · linarith only [h348, h349, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h384 | h384
      · rcases p0_3 (m.d 0 3) (by simp) with h385 | h385
        · rcases p0_3 (m.d 0 4) (by simp) with h386 | h386
          · linarith only [h386, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h388 | h388
            · rcases m.htr 0 1 2 (by decide) (by decide) with h389 | h389
              · linarith only [h348, h389, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h348, h384, h389, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h388, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h393 | h393
          · linarith only [h393, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h395 | h395
            · rcases m.htr 0 1 2 (by decide) (by decide) with h396 | h396
              · linarith only [h348, h384, h396, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h348, h384, h396, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h395, hlam, p0_0]
      · linarith only [h384, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_I_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5ehi := hb5.2.1
  have h2ehi := hb2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h3 | h3
    · rcases p0_3 (m.d 0 2) (by simp) with h4 | h4
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · linarith only [h5, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · linarith only [h4, h9, hlam]
              · linarith only [h9, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h8, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h13 | h13
            · rcases m.htr 0 1 2 (by decide) (by decide) with h14 | h14
              · linarith only [h14, h4, hlam]
              · linarith only [h14, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h13, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · linarith only [h3, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · rcases p0_3 (m.d 0 2) (by simp) with h21 | h21
      · rcases p0_3 (m.d 0 3) (by simp) with h22 | h22
        · rcases p0_3 (m.d 0 4) (by simp) with h23 | h23
          · linarith only [h23, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h25 | h25
            · rcases m.htr 0 1 2 (by decide) (by decide) with h26 | h26
              · linarith only [h21, h26, hlam]
              · linarith only [h26, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h25, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h30 | h30
          · linarith only [h30, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h32 | h32
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · linarith only [h21, h33, hlam]
              · linarith only [h22, h33, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h32, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h21, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · linarith only [h20, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h42 | h42
      · rcases p0_3 (m.d 0 3) (by simp) with h43 | h43
        · rcases p0_3 (m.d 0 4) (by simp) with h44 | h44
          · rcases p0_3 (m.d 0 5) (by simp) with h45 | h45
            · rcases m.htr 0 1 2 (by decide) (by decide) with h46 | h46
              · linarith only [h46, hlam, p0_0]
              · linarith only [h46, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h45, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h50 | h50
            · rcases m.htr 0 1 2 (by decide) (by decide) with h51 | h51
              · linarith only [h51, hlam, p0_0]
              · linarith only [h51, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h50, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h55 | h55
          · rcases p0_3 (m.d 0 5) (by simp) with h56 | h56
            · rcases m.htr 0 1 2 (by decide) (by decide) with h57 | h57
              · linarith only [h57, hlam, p0_0]
              · linarith only [h57, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h56, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h61 | h61
            · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
              · linarith only [h62, hlam, p0_0]
              · linarith only [h62, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h61, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h68 | h68
    · rcases p0_3 (m.d 0 2) (by simp) with h69 | h69
      · rcases p0_3 (m.d 0 3) (by simp) with h70 | h70
        · linarith only [h70, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 0 5) (by simp) with h73 | h73
            · rcases m.htr 0 1 2 (by decide) (by decide) with h74 | h74
              · rcases m.htr 0 1 3 (by decide) (by decide) with h75 | h75
                · rcases m.htr 0 1 4 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h78 | h78
                      · linarith only [h74, h78, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h78, hlam, p0_0]
                    · linarith only [h74, h77, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h74, h75, h76, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h74, h75, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h68, h74, hlam]
            · linarith only [h73, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h86 | h86
            · rcases m.htr 0 1 2 (by decide) (by decide) with h87 | h87
              · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
                · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h91 | h91
                      · linarith only [h87, h91, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h91, hlam, p0_0]
                    · linarith only [h87, h90, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h87, h88, h89, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h87, h88, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h68, h87, hlam]
            · linarith only [h68, h86, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h69, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h100 | h100
      · rcases p0_3 (m.d 0 3) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
            · rcases m.htr 0 1 2 (by decide) (by decide) with h105 | h105
              · linarith only [h105, h68, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h105, h68, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h104, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h109 | h109
            · rcases m.htr 0 1 2 (by decide) (by decide) with h110 | h110
              · linarith only [h110, h68, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h110, h68, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h109, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h115 | h115
    · rcases p0_3 (m.d 0 2) (by simp) with h116 | h116
      · rcases p0_3 (m.d 0 3) (by simp) with h117 | h117
        · rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
          · linarith only [h118, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h120 | h120
            · rcases m.htr 0 1 2 (by decide) (by decide) with h121 | h121
              · rcases m.htr 0 1 3 (by decide) (by decide) with h122 | h122
                · rcases m.htr 0 1 4 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h125 | h125
                      · linarith only [h117, h125, hlam]
                      · linarith only [h125, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h121, h123, h124, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h121, h123, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h121, h122, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h115, h121, hlam]
            · linarith only [h120, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
          · linarith only [h133, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h135 | h135
            · rcases m.htr 0 1 2 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 1 3 (by decide) (by decide) with h137 | h137
                · rcases m.htr 0 1 4 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h140 | h140
                      · linarith only [h117, h136, h140, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h117, h140, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h117, h136, h137, h139, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h117, h136, h137, h138, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h117, h136, h137, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h115, h136, hlam]
            · linarith only [h135, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h116, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h149 | h149
      · rcases p0_3 (m.d 0 3) (by simp) with h150 | h150
        · rcases p0_3 (m.d 0 4) (by simp) with h151 | h151
          · linarith only [h151, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h153 | h153
            · rcases m.htr 0 1 2 (by decide) (by decide) with h154 | h154
              · linarith only [h115, h154, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h115, h154, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h153, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h158 | h158
          · linarith only [h158, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h160 | h160
            · rcases m.htr 0 1 2 (by decide) (by decide) with h161 | h161
              · linarith only [h115, h161, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h115, h161, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h160, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h149, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h167 | h167
    · linarith only [h167, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h169 | h169
      · rcases p0_3 (m.d 0 3) (by simp) with h170 | h170
        · rcases p0_3 (m.d 0 4) (by simp) with h171 | h171
          · rcases p0_3 (m.d 0 5) (by simp) with h172 | h172
            · rcases m.htr 0 1 2 (by decide) (by decide) with h173 | h173
              · linarith only [h173, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h169, h173, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h169, h172, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h177 | h177
            · rcases m.htr 0 1 2 (by decide) (by decide) with h178 | h178
              · linarith only [h169, h178, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h169, h178, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h169, h177, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h170, hlam, p0_0]
      · linarith only [h169, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h186 | h186
    · rcases p0_3 (m.d 0 2) (by simp) with h187 | h187
      · rcases p0_3 (m.d 0 3) (by simp) with h188 | h188
        · rcases p0_3 (m.d 0 4) (by simp) with h189 | h189
          · linarith only [h189, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h191 | h191
            · rcases m.htr 0 1 2 (by decide) (by decide) with h192 | h192
              · rcases m.htr 0 1 3 (by decide) (by decide) with h193 | h193
                · rcases m.htr 0 1 4 (by decide) (by decide) with h194 | h194
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h195 | h195
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h196 | h196
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h197 | h197
                        · linarith only [h192, h196, h197, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
                        · linarith only [h196, h197, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h187, h196, hlam]
                    · linarith only [h193, h194, h195, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h193, h194, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h186, h193, hlam]
              · linarith only [h186, h192, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h186, h191, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h188, hlam, p0_0]
      · linarith only [h186, h187, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h208 | h208
      · rcases p0_3 (m.d 0 3) (by simp) with h209 | h209
        · rcases p0_3 (m.d 0 4) (by simp) with h210 | h210
          · linarith only [h210, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h212 | h212
            · rcases m.htr 0 1 2 (by decide) (by decide) with h213 | h213
              · linarith only [h186, h213, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h186, h208, h213, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h208, h212, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h209, hlam, p0_0]
      · linarith only [h208, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h220 | h220
    · linarith only [h220, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h222 | h222
      · rcases p0_3 (m.d 0 3) (by simp) with h223 | h223
        · rcases p0_3 (m.d 0 4) (by simp) with h224 | h224
          · rcases p0_3 (m.d 0 5) (by simp) with h225 | h225
            · rcases m.htr 0 1 2 (by decide) (by decide) with h226 | h226
              · linarith only [h222, h226, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h222, h226, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h222, h225, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h224, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 0 5) (by simp) with h232 | h232
            · rcases m.htr 0 1 2 (by decide) (by decide) with h233 | h233
              · linarith only [h222, h233, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h222, h233, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h222, h232, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h231, hlam, p0_0]
      · linarith only [h222, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h240 | h240
    · rcases p0_3 (m.d 0 2) (by simp) with h241 | h241
      · rcases p0_3 (m.d 0 3) (by simp) with h242 | h242
        · linarith only [h242, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h244 | h244
          · rcases p0_3 (m.d 0 5) (by simp) with h245 | h245
            · rcases m.htr 0 1 2 (by decide) (by decide) with h246 | h246
              · rcases m.htr 0 1 3 (by decide) (by decide) with h247 | h247
                · rcases m.htr 0 1 4 (by decide) (by decide) with h248 | h248
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h249 | h249
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h250 | h250
                      · linarith only [h241, h246, h250, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h241, h250, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h241, h246, h247, h249, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h240, h248, hlam]
                · linarith only [h241, h246, h247, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h240, h246, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h240, h245, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h244, hlam, p0_0]
      · linarith only [h240, h241, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h260 | h260
      · rcases p0_3 (m.d 0 3) (by simp) with h261 | h261
        · linarith only [h261, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 0 5) (by simp) with h264 | h264
            · rcases m.htr 0 1 2 (by decide) (by decide) with h265 | h265
              · linarith only [h240, h265, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h240, h260, h265, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h260, h264, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h263, hlam, p0_0]
      · linarith only [h260, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h273 | h273
    · linarith only [h273, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h275 | h275
      · rcases p0_3 (m.d 0 3) (by simp) with h276 | h276
        · rcases p0_3 (m.d 0 4) (by simp) with h277 | h277
          · rcases p0_3 (m.d 0 5) (by simp) with h278 | h278
            · rcases m.htr 0 1 2 (by decide) (by decide) with h279 | h279
              · linarith only [h275, h279, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h275, h279, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h278, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h283 | h283
            · rcases m.htr 0 1 2 (by decide) (by decide) with h284 | h284
              · linarith only [h275, h284, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h275, h284, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h283, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h288 | h288
          · rcases p0_3 (m.d 0 5) (by simp) with h289 | h289
            · rcases m.htr 0 1 2 (by decide) (by decide) with h290 | h290
              · linarith only [h275, h290, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h275, h290, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h289, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h294 | h294
            · rcases m.htr 0 1 2 (by decide) (by decide) with h295 | h295
              · linarith only [h275, h295, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h275, h295, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h294, hlam, p0_0]
      · linarith only [h275, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h301 | h301
    · rcases p0_3 (m.d 0 2) (by simp) with h302 | h302
      · rcases p0_3 (m.d 0 3) (by simp) with h303 | h303
        · linarith only [h303, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h305 | h305
          · rcases p0_3 (m.d 0 5) (by simp) with h306 | h306
            · rcases m.htr 0 1 2 (by decide) (by decide) with h307 | h307
              · rcases m.htr 0 1 3 (by decide) (by decide) with h308 | h308
                · rcases m.htr 0 1 4 (by decide) (by decide) with h309 | h309
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h310 | h310
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h311 | h311
                      · linarith only [h302, h307, h311, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h302, h311, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h301, h310, hlam]
                  · linarith only [h302, h307, h308, h309, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h302, h307, h308, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h301, h307, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h306, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h319 | h319
            · rcases m.htr 0 1 2 (by decide) (by decide) with h320 | h320
              · rcases m.htr 0 1 3 (by decide) (by decide) with h321 | h321
                · rcases m.htr 0 1 4 (by decide) (by decide) with h322 | h322
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h323 | h323
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h324 | h324
                      · linarith only [h302, h320, h324, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h302, h324, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h301, h323, hlam]
                  · linarith only [h302, h320, h321, h322, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h302, h320, h321, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h301, h320, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h319, hlam, p0_0]
      · linarith only [h301, h302, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h333 | h333
      · rcases p0_3 (m.d 0 3) (by simp) with h334 | h334
        · linarith only [h334, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h336 | h336
          · rcases p0_3 (m.d 0 5) (by simp) with h337 | h337
            · rcases m.htr 0 1 2 (by decide) (by decide) with h338 | h338
              · linarith only [h301, h338, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h301, h333, h338, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h337, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h342 | h342
            · rcases m.htr 0 1 2 (by decide) (by decide) with h343 | h343
              · linarith only [h301, h333, h343, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h301, h333, h343, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h342, hlam, p0_0]
      · linarith only [h333, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h348 | h348
    · rcases p0_3 (m.d 0 2) (by simp) with h349 | h349
      · rcases p0_3 (m.d 0 3) (by simp) with h350 | h350
        · rcases p0_3 (m.d 0 4) (by simp) with h351 | h351
          · linarith only [h351, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h353 | h353
            · rcases m.htr 0 1 2 (by decide) (by decide) with h354 | h354
              · rcases m.htr 0 1 3 (by decide) (by decide) with h355 | h355
                · rcases m.htr 0 1 4 (by decide) (by decide) with h356 | h356
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h357 | h357
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h358 | h358
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h359 | h359
                        · linarith only [h350, h354, h358, h359, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
                        · linarith only [h350, h358, h359, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h349, h356, h358, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h348, h357, hlam]
                  · linarith only [h348, h356, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h349, h354, h355, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h348, h354, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h353, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h368 | h368
          · linarith only [h368, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h370 | h370
            · rcases m.htr 0 1 2 (by decide) (by decide) with h371 | h371
              · rcases m.htr 0 1 3 (by decide) (by decide) with h372 | h372
                · rcases m.htr 0 1 4 (by decide) (by decide) with h373 | h373
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h374 | h374
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h375 | h375
                      · linarith only [h349, h350, h371, h375, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h349, h350, h375, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h348, h374, hlam]
                  · linarith only [h349, h350, h371, h372, h373, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h349, h350, h371, h372, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h348, h350, h371, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h370, hlam, p0_0]
      · linarith only [h348, h349, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h384 | h384
      · rcases p0_3 (m.d 0 3) (by simp) with h385 | h385
        · rcases p0_3 (m.d 0 4) (by simp) with h386 | h386
          · linarith only [h386, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h388 | h388
            · rcases m.htr 0 1 2 (by decide) (by decide) with h389 | h389
              · linarith only [h348, h389, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h348, h384, h389, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h388, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h393 | h393
          · linarith only [h393, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h395 | h395
            · rcases m.htr 0 1 2 (by decide) (by decide) with h396 | h396
              · linarith only [h348, h384, h396, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h348, h384, h396, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h395, hlam, p0_0]
      · linarith only [h384, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_I_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_I_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_I_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h2ehi := hb2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht23, ht34, ht45, p0_1, u2ehi4, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht23, ht34, ht45, p0_1, u2ehi4, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_I_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2elo := hb2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · linarith only [h7, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h10 | h10
            · linarith only [h10, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h10, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · linarith only [h14, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h14, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h17 | h17
            · linarith only [h17, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h17, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h21 | h21
    · rcases p0_3 (m.d 0 2) (by simp) with h22 | h22
      · linarith only [h22, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h24 | h24
        · linarith only [h24, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h26 | h26
          · rcases p0_3 (m.d 0 5) (by simp) with h27 | h27
            · linarith only [h22, h27, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h27, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h30 | h30
            · linarith only [h30, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h30, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · rcases p0_3 (m.d 0 2) (by simp) with h35 | h35
      · linarith only [h35, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h37 | h37
        · rcases p0_3 (m.d 0 4) (by simp) with h38 | h38
          · linarith only [h38, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
            · linarith only [h35, h40, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h40, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h43 | h43
          · linarith only [h43, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h45 | h45
            · linarith only [h37, h45, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h45, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h34, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, p0_1, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h55 | h55
    · linarith only [h55, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h57 | h57
      · linarith only [h57, hc01, hlam, hphi, ht12, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h59 | h59
        · rcases p0_3 (m.d 0 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 0 5) (by simp) with h61 | h61
            · linarith only [h61, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h61, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h64 | h64
            · linarith only [h64, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h64, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h59, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h68 | h68
    · rcases p0_3 (m.d 0 2) (by simp) with h69 | h69
      · linarith only [h69, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h71 | h71
        · rcases p0_3 (m.d 0 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 0 5) (by simp) with h73 | h73
            · linarith only [h73, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h68, h73, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h76 | h76
            · linarith only [h76, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h68, h76, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h71, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h80 | h80
      · linarith only [h80, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h82 | h82
        · rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 0 5) (by simp) with h84 | h84
            · linarith only [h68, h84, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h84, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h87 | h87
            · linarith only [h87, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h87, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h82, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h92 | h92
    · rcases p0_3 (m.d 0 2) (by simp) with h93 | h93
      · linarith only [h93, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h95 | h95
        · rcases p0_3 (m.d 0 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h98 | h98
            · linarith only [h93, h98, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h92, h98, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h95, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h102 | h102
      · linarith only [h102, h92, hc01, hlam, hphi, ht12, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h104 | h104
        · rcases p0_3 (m.d 0 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h107 | h107
            · linarith only [h107, h92, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h107, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h104, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h112 | h112
    · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h114 | h114
      · linarith only [h114, hc01, hlam, hphi, ht12, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h116 | h116
        · rcases p0_3 (m.d 0 4) (by simp) with h117 | h117
          · rcases p0_3 (m.d 0 5) (by simp) with h118 | h118
            · linarith only [h118, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h118, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h117, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h122 | h122
          · rcases p0_3 (m.d 0 5) (by simp) with h123 | h123
            · linarith only [h123, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h123, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h122, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h127 | h127
    · rcases p0_3 (m.d 0 2) (by simp) with h128 | h128
      · linarith only [h128, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h130 | h130
        · rcases p0_3 (m.d 0 4) (by simp) with h131 | h131
          · rcases p0_3 (m.d 0 5) (by simp) with h132 | h132
            · linarith only [h132, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h127, h132, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h131, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h136 | h136
          · rcases p0_3 (m.d 0 5) (by simp) with h137 | h137
            · linarith only [h137, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h127, h137, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h136, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h141 | h141
      · linarith only [h141, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h143 | h143
        · rcases p0_3 (m.d 0 4) (by simp) with h144 | h144
          · rcases p0_3 (m.d 0 5) (by simp) with h145 | h145
            · linarith only [h127, h145, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h143, h145, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h144, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h149 | h149
          · rcases p0_3 (m.d 0 5) (by simp) with h150 | h150
            · linarith only [h150, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h150, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h149, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h154 | h154
    · rcases p0_3 (m.d 0 2) (by simp) with h155 | h155
      · linarith only [h155, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h157 | h157
        · linarith only [h157, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 0 5) (by simp) with h160 | h160
            · linarith only [h155, h160, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h154, h160, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h159, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h164 | h164
      · linarith only [h154, h164, hc01, hlam, hphi, ht12, p0_1, u2elo0]
      · rcases p0_3 (m.d 0 3) (by simp) with h166 | h166
        · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 0 5) (by simp) with h169 | h169
            · linarith only [h154, h169, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h169, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h168, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_I_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · linarith only [h7, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h10 | h10
            · linarith only [h10, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h10, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · linarith only [h14, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h14, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h17 | h17
            · linarith only [h17, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h17, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h21 | h21
    · rcases p0_3 (m.d 0 2) (by simp) with h22 | h22
      · rcases p0_3 (m.d 0 3) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 0 5) (by simp) with h26 | h26
            · linarith only [h26, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h26, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · linarith only [h29, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h29, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 0 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h35, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h38 | h38
            · linarith only [h38, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h38, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h42 | h42
    · rcases p0_3 (m.d 0 2) (by simp) with h43 | h43
      · rcases p0_3 (m.d 0 3) (by simp) with h44 | h44
        · rcases p0_3 (m.d 0 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h47 | h47
            · linarith only [h47, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h47, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h52, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h55 | h55
        · rcases p0_3 (m.d 0 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h58, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h63 | h63
            · linarith only [h55, h63, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h63, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h70 | h70
      · rcases p0_3 (m.d 0 3) (by simp) with h71 | h71
        · rcases p0_3 (m.d 0 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 0 5) (by simp) with h73 | h73
            · linarith only [h73, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h73, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h76 | h76
            · linarith only [h76, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h76, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 0 5) (by simp) with h80 | h80
            · linarith only [h80, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h80, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h83 | h83
            · linarith only [h83, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h83, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h70, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h88 | h88
    · rcases p0_3 (m.d 0 2) (by simp) with h89 | h89
      · rcases p0_3 (m.d 0 3) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 0 5) (by simp) with h93 | h93
            · linarith only [h93, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h88, h93, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h96 | h96
            · linarith only [h96, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h88, h96, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h100 | h100
      · rcases p0_3 (m.d 0 3) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h104, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h107 | h107
            · linarith only [h107, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h107, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h111 | h111
    · rcases p0_3 (m.d 0 2) (by simp) with h112 | h112
      · rcases p0_3 (m.d 0 3) (by simp) with h113 | h113
        · rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h116 | h116
            · linarith only [h116, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h111, h116, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h111, h121, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h125 | h125
      · rcases p0_3 (m.d 0 3) (by simp) with h126 | h126
        · rcases p0_3 (m.d 0 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h129, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
            · linarith only [h126, h134, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h134, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h125, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h141 | h141
      · rcases p0_3 (m.d 0 3) (by simp) with h142 | h142
        · rcases p0_3 (m.d 0 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 0 5) (by simp) with h144 | h144
            · linarith only [h144, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h144, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h147 | h147
            · linarith only [h147, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h147, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h151 | h151
        · rcases p0_3 (m.d 0 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 0 5) (by simp) with h153 | h153
            · linarith only [h153, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h153, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h156 | h156
            · linarith only [h156, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h156, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h151, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h160 | h160
    · rcases p0_3 (m.d 0 2) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h163 | h163
        · rcases p0_3 (m.d 0 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 0 5) (by simp) with h165 | h165
            · linarith only [h165, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h160, h165, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h168 | h168
            · linarith only [h168, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h168, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h174 | h174
        · rcases p0_3 (m.d 0 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 0 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h176, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h179 | h179
            · linarith only [h179, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h179, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h174, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h184 | h184
    · rcases p0_3 (m.d 0 2) (by simp) with h185 | h185
      · rcases p0_3 (m.d 0 3) (by simp) with h186 | h186
        · rcases p0_3 (m.d 0 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h189 | h189
            · linarith only [h189, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h184, h189, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h193 | h193
        · rcases p0_3 (m.d 0 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h184, h196, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h200 | h200
      · rcases p0_3 (m.d 0 3) (by simp) with h201 | h201
        · rcases p0_3 (m.d 0 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h200, h204, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h208 | h208
        · rcases p0_3 (m.d 0 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h211 | h211
            · linarith only [h200, h211, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h211, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h208, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h218 | h218
      · rcases p0_3 (m.d 0 3) (by simp) with h219 | h219
        · rcases p0_3 (m.d 0 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 0 5) (by simp) with h221 | h221
            · linarith only [h221, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h218, h221, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 0 5) (by simp) with h226 | h226
            · linarith only [h226, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h226, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h230 | h230
        · rcases p0_3 (m.d 0 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 0 5) (by simp) with h232 | h232
            · linarith only [h232, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h230, h232, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 0 5) (by simp) with h237 | h237
            · linarith only [h237, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h237, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h236, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h241 | h241
    · rcases p0_3 (m.d 0 2) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h244 | h244
        · rcases p0_3 (m.d 0 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 0 5) (by simp) with h246 | h246
            · linarith only [h246, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h241, h246, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 0 5) (by simp) with h251 | h251
            · linarith only [h251, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h241, h251, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h257 | h257
        · rcases p0_3 (m.d 0 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 0 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h257, h259, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 0 5) (by simp) with h264 | h264
            · linarith only [h264, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h264, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h263, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h268 | h268
    · rcases p0_3 (m.d 0 2) (by simp) with h269 | h269
      · rcases p0_3 (m.d 0 3) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 0 5) (by simp) with h273 | h273
            · linarith only [h273, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h268, h273, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 0 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h268, h280, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h284 | h284
      · rcases p0_3 (m.d 0 3) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 0 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h284, h288, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 0 5) (by simp) with h295 | h295
            · linarith only [h284, h295, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h295, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h294, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_I_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2ehi := hb2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h3 | h3
    · rcases p0_3 (m.d 0 2) (by simp) with h4 | h4
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · linarith only [h5, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
            · linarith only [h8, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h8, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
            · linarith only [h11, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h11, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · linarith only [h3, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · rcases p0_3 (m.d 0 2) (by simp) with h17 | h17
      · rcases p0_3 (m.d 0 3) (by simp) with h18 | h18
        · rcases p0_3 (m.d 0 4) (by simp) with h19 | h19
          · linarith only [h19, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h21 | h21
            · linarith only [h21, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h21, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h24 | h24
          · linarith only [h24, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h26 | h26
            · linarith only [h18, h26, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h26, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h17, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · linarith only [h16, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h34 | h34
      · rcases p0_3 (m.d 0 3) (by simp) with h35 | h35
        · rcases p0_3 (m.d 0 4) (by simp) with h36 | h36
          · rcases p0_3 (m.d 0 5) (by simp) with h37 | h37
            · linarith only [h37, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h37, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
            · linarith only [h40, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h40, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h43 | h43
          · rcases p0_3 (m.d 0 5) (by simp) with h44 | h44
            · linarith only [h44, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h44, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h47 | h47
            · linarith only [h47, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h47, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h34, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h52 | h52
    · rcases p0_3 (m.d 0 2) (by simp) with h53 | h53
      · rcases p0_3 (m.d 0 3) (by simp) with h54 | h54
        · linarith only [h54, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h56 | h56
          · rcases p0_3 (m.d 0 5) (by simp) with h57 | h57
            · linarith only [h57, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h52, h57, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h60 | h60
            · linarith only [h60, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h52, h60, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h53, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h64 | h64
      · rcases p0_3 (m.d 0 3) (by simp) with h65 | h65
        · linarith only [h65, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h67 | h67
          · rcases p0_3 (m.d 0 5) (by simp) with h68 | h68
            · linarith only [h52, h68, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h68, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h71 | h71
            · linarith only [h71, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h71, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h64, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h75 | h75
    · rcases p0_3 (m.d 0 2) (by simp) with h76 | h76
      · rcases p0_3 (m.d 0 3) (by simp) with h77 | h77
        · rcases p0_3 (m.d 0 4) (by simp) with h78 | h78
          · linarith only [h78, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h80 | h80
            · linarith only [h80, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h75, h80, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
          · linarith only [h83, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h85 | h85
            · linarith only [h77, h85, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h85, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h76, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h89 | h89
      · rcases p0_3 (m.d 0 3) (by simp) with h90 | h90
        · rcases p0_3 (m.d 0 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h93 | h93
            · linarith only [h75, h93, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h93, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h98 | h98
            · linarith only [h90, h98, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h98, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h89, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h103 | h103
    · linarith only [h103, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h105 | h105
      · rcases p0_3 (m.d 0 3) (by simp) with h106 | h106
        · rcases p0_3 (m.d 0 4) (by simp) with h107 | h107
          · rcases p0_3 (m.d 0 5) (by simp) with h108 | h108
            · linarith only [h108, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h108, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h111 | h111
            · linarith only [h111, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h111, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h106, hlam, p0_0]
      · linarith only [h105, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h118 | h118
    · rcases p0_3 (m.d 0 2) (by simp) with h119 | h119
      · rcases p0_3 (m.d 0 3) (by simp) with h120 | h120
        · rcases p0_3 (m.d 0 4) (by simp) with h121 | h121
          · linarith only [h121, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h123 | h123
            · linarith only [h123, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h118, h123, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h120, hlam, p0_0]
      · linarith only [h118, h119, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h128 | h128
      · rcases p0_3 (m.d 0 3) (by simp) with h129 | h129
        · rcases p0_3 (m.d 0 4) (by simp) with h130 | h130
          · linarith only [h130, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h132 | h132
            · linarith only [h118, h132, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h128, h132, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h129, hlam, p0_0]
      · linarith only [h128, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h138 | h138
    · linarith only [h138, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h140 | h140
      · rcases p0_3 (m.d 0 3) (by simp) with h141 | h141
        · rcases p0_3 (m.d 0 4) (by simp) with h142 | h142
          · rcases p0_3 (m.d 0 5) (by simp) with h143 | h143
            · linarith only [h143, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h140, h143, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h142, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h147 | h147
          · rcases p0_3 (m.d 0 5) (by simp) with h148 | h148
            · linarith only [h148, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h148, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h147, hlam, p0_0]
      · linarith only [h140, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h154 | h154
    · rcases p0_3 (m.d 0 2) (by simp) with h155 | h155
      · rcases p0_3 (m.d 0 3) (by simp) with h156 | h156
        · linarith only [h156, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h158 | h158
          · rcases p0_3 (m.d 0 5) (by simp) with h159 | h159
            · linarith only [h159, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h154, h159, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h158, hlam, p0_0]
      · linarith only [h154, h155, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h164 | h164
      · rcases p0_3 (m.d 0 3) (by simp) with h165 | h165
        · linarith only [h165, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h167 | h167
          · rcases p0_3 (m.d 0 5) (by simp) with h168 | h168
            · linarith only [h154, h168, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h164, h168, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h167, hlam, p0_0]
      · linarith only [h164, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht23, ht34, ht45, p0_1, u2ehi0, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_L_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
          · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h4, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
              · linarith only [h4, h5, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · linarith only [h2, h4, h5, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
          · linarith only [h0, h6, hc34, hlam, hphi, ht23, u2ehi0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
            · linarith only [h13, h14, h2, h5, hc23, hlam, hphi, u2ehi0]
            · linarith only [h14, h2, hc45, hlam, hphi, ht23, ht34, u2ehi0]
          · linarith only [h13, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
        · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, h4, hc23, hlam, hphi, u2ehi0]
          · linarith only [h0, h19, hc34, hlam, hphi, ht23, u2ehi0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
          · linarith only [h0, h22, h4, hc23, hlam, hphi, u2ehi0]
          · linarith only [h0, h22, hc34, hlam, hphi, ht23, u2ehi0]

theorem n7l_sBT2_H_L_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · linarith only [h0, h1, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
      · linarith only [h1, h5, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
        · linarith only [h0, h7, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
        · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h10 | h10
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
        · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
          · linarith only [h10, h13, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
          · linarith only [h13, hc23, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h0, h12, hc01, hlam, hphi, ht12, u2elo4]
      · linarith only [h0, h11, hc01, hlam, hphi, ht12, u2elo2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
      · linarith only [h10, h18, hc02, hlam, hphi, u2elo1]
      · linarith only [h0, h18, hc01, hlam, hphi, ht12, u2elo2]

theorem n7l_sBT2_H_L_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h2bigk := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h0, h1, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · linarith only [h3, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
          · linarith only [h0, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h1, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h8, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 2 5 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
          · linarith only [h0, h1, h13, h15, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
            · linarith only [h0, h17, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h13, h17, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h14, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h21 | h21
        · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
          · linarith only [h0, h1, h21, h22, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
            · linarith only [h0, h13, h21, h24, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
              · linarith only [h0, h26, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · linarith only [h21, h26, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h21, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h30 | h30
    · rcases m.htr 0 2 4 (by decide) (by decide) with h31 | h31
      · rcases m.htr 0 2 5 (by decide) (by decide) with h32 | h32
        · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
          · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
            · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
              · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                · linarith only [h30, h36, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                  · linarith only [h31, h36, h38, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h38, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h32, h35, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h31, h34, hlam]
          · linarith only [h0, h30, h33, hlam]
        · linarith only [h32, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h45 | h45
        · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
          · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
            · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
              · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                · linarith only [h30, h49, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
                  · linarith only [h30, h31, h51, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h51, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h31, h45, h47, h48, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
              · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                · linarith only [h30, h31, h56, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h58 | h58
                  · linarith only [h30, h31, h58, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h58, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h31, h45, h55, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
          · linarith only [h0, h30, h46, hlam]
        · linarith only [h45, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h64 | h64
      · rcases m.htr 0 2 5 (by decide) (by decide) with h65 | h65
        · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
          · rcases m.htr 1 2 4 (by decide) (by decide) with h67 | h67
            · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
              · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                    · linarith only [h64, h71, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h71, hc24, hlam, hphi, ht45, u5elo4]
                  · linarith only [h30, h64, h69, h70, hc34, hlam, hphi, ht45, u5elo3]
                · linarith only [h30, h64, h69, hlam]
              · linarith only [h30, h65, h66, h68, hlam]
            · linarith only [h30, h64, h66, h67, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
            · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
              · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                · rcases m.htr 2 3 5 (by decide) (by decide) with h81 | h81
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h82 | h82
                    · linarith only [h64, h82, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h82, hc24, hlam, hphi, ht45, u5elo4]
                  · linarith only [h66, h81, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h66, h80, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h65, h79, hlam]
            · linarith only [h0, h64, h78, hlam]
        · linarith only [h65, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h90 | h90
        · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
          · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
            · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
              · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
                      · rcases h2bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h0, hlam, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h30, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h64, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h95, h97, hc45, hlam, hphi, ht0b, ht5b, p98_1, u0elo1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          rcases p98_3 (m.d 0 2) (by simp) with h104 | h104
                          · linarith only [h0, h104, hlam]
                          · rcases p98_3 (m.d 1 2) (by simp) with h106 | h106
                            · rcases p98_3 (m.d 2 3) (by simp) with h107 | h107
                              · linarith only [h107, h91, hlam]
                              · linarith only [h107, h30, hlam]
                            · linarith only [h0, h106, hlam]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h0, h64, h94, hc01, hc12, hlam, hphi, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h64, h90, h95, h97, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h64, h90, h91, h94, hlam, p98_2]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h90, h91, h95, h97, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h91, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h64, h90, h91, h95, h97, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          rcases p98_3 (m.d 0 2) (by simp) with h119 | h119
                          · linarith only [h119, h30, hlam]
                          · linarith only [h119, h90, hlam]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h90, h92, h95, h97, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h92, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h94, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          rcases p98_3 (m.d 0 2) (by simp) with h126 | h126
                          · linarith only [h126, h64, hlam]
                          · linarith only [h126, h90, hlam]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h90, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h93, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h95, hlam, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h96, hlam, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                      · linarith only [h97, hc34, hlam, hphi, ht45, u5elo4]
                    · linarith only [h64, h96, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h64, h90, h94, h95, hc25, hlam, hphi, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h137 | h137
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h138 | h138
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h139 | h139
                      · rcases h2bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [hlam, p140_0]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h0, hlam, p140_1]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h30, hlam, p140_0]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h64, hlam, p140_0]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h137, h139, hc45, hlam, hphi, ht0b, ht5b, p140_1, u0elo1]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          rcases p140_3 (m.d 0 2) (by simp) with h146 | h146
                          · linarith only [h0, h146, hlam]
                          · rcases p140_3 (m.d 1 2) (by simp) with h148 | h148
                            · rcases p140_3 (m.d 2 3) (by simp) with h149 | h149
                              · linarith only [h149, h91, hlam]
                              · linarith only [h149, h30, hlam]
                            · linarith only [h0, h148, hlam]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [hlam, p140_0]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h0, h30, hc01, hc12, hlam, hphi, p140_1]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h137, h139, h30, h90, h94, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p140_1]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h30, h90, h91, hlam, p140_2]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h137, h139, h90, h91, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p140_1]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h91, hlam, p140_0]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [hlam, p140_0]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h94, hlam, p140_1]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          rcases p140_3 (m.d 0 2) (by simp) with h161 | h161
                          · linarith only [h161, h30, hlam]
                          · linarith only [h161, h90, hlam]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h137, h139, h90, h92, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p140_1]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h92, hlam, p140_0]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h137, h139, h30, h90, h92, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p140_1]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [hlam, p140_0]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          rcases p140_3 (m.d 0 2) (by simp) with h168 | h168
                          · linarith only [h168, h64, hlam]
                          · linarith only [h168, h90, hlam]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h90, hlam, p140_0]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h93, hlam, p140_0]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h137, hlam, p140_1]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [h138, hlam, p140_1]
                        · have p140_0 := h140c.1
                          have p140_1 := h140c.2.1
                          have p140_2 := h140c.2.2.1
                          have p140_3 := h140c.2.2.2
                          linarith only [hlam, p140_0]
                      · linarith only [h139, hc34, hlam, hphi, ht45, u5elo4]
                    · linarith only [h138, hc24, hlam, hphi, ht45, u5elo4]
                  · linarith only [h137, h30, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h90, h93, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h30, h91, h92, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
            · linarith only [h181, h64, h90, h91, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
              · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                      · rcases h2bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h0, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h30, hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h64, hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h185, h187, hc45, hlam, hphi, ht0b, ht5b, p188_1, u0elo1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h181, h184, hc02, hc23, hlam, hphi, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h91, hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h181, hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          rcases p188_3 (m.d 0 2) (by simp) with h198 | h198
                          · linarith only [h0, h198, hlam]
                          · linarith only [h198, h90, hlam]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          rcases p188_3 (m.d 0 2) (by simp) with h201 | h201
                          · linarith only [h201, hlam, p188_0]
                          · rcases p188_3 (m.d 1 2) (by simp) with h203 | h203
                            · linarith only [h203, h91, hlam]
                            · linarith only [h0, h203, hlam]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h185, h187, h64, h90, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          rcases p188_3 (m.d 0 2) (by simp) with h209 | h209
                          · linarith only [h209, h30, hlam]
                          · linarith only [h209, h90, hlam]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          rcases p188_3 (m.d 0 2) (by simp) with h212 | h212
                          · linarith only [h212, hlam, p188_0]
                          · rcases p188_3 (m.d 1 2) (by simp) with h214 | h214
                            · linarith only [h181, h214, hlam]
                            · linarith only [h0, h214, hlam]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h0, h184, hc01, hc23, hlam, hphi, ht12, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h184, hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          rcases p188_3 (m.d 0 2) (by simp) with h220 | h220
                          · linarith only [h220, h64, hlam]
                          · linarith only [h220, h90, hlam]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h90, hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h183, hlam, p188_0]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h185, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [h186, hlam, p188_1]
                        · have p188_0 := h188c.1
                          have p188_1 := h188c.2.1
                          have p188_2 := h188c.2.2.1
                          have p188_3 := h188c.2.2.2
                          linarith only [hlam, p188_0]
                      · linarith only [h187, hc34, hlam, hphi, ht45, u5elo4]
                    · linarith only [h181, h186, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h185, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h184, h91, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h183, h90, hlam]
        · linarith only [h90, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

theorem n7l_sBT2_H_L_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h2ehi := hb2.1
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo2]

theorem n7l_sBT2_H_L_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht0b, ht5b, u0elo4, u5ehi0]

theorem n7l_sBT2_H_L_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht0b, ht5b, u0elo4, u5ehi0]

theorem n7l_sBT2_H_L_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht0b, ht5b, u0elo4, u5ehi0]

theorem n7l_sBT2_H_L_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.2.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
        · linarith only [h0, h1, h3, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · linarith only [h0, h1, h5, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h8 | h8
    · linarith only [h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h10 | h10
      · linarith only [h10, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
        · linarith only [h0, h10, h12, hc01, hlam, hphi, ht12, u2elo1]
        · linarith only [h0, h12, hc01, hlam, hphi, ht12, u2elo4]

theorem n7l_sBT2_H_L_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.2.1
  have h2ehi := hb2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
      · linarith only [h0, h2, h4, hc23, hlam, hphi, u2ehi0]
      · linarith only [h0, h4, hc35, hlam, hphi, ht23, u2ehi0]

theorem n7l_sBT2_H_L_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_L_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_H_L_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h2ehi := hb2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi4]
  · linarith only [h0, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem n7l_sBT2_H_L_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
    · linarith only [h0, h1, hc14, hlam, hphi, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6 | h6
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7 | h7
        · linarith only [h7, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi7]
        · linarith only [h6, h7, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h10 | h10
        · linarith only [h10, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi7]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h12 | h12
          · linarith only [h12, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi9]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
            · linarith only [h14, h6, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h12, h14, h16, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h16, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]

theorem n7l_sBT2_H_L_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h5 | h5
      · linarith only [h5, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
      · linarith only [h0, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h8 | h8
    · rcases m.htr 0 1 5 (by decide) (by decide) with h9 | h9
      · linarith only [h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
      · linarith only [h8, h9, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h12 | h12
      · linarith only [h12, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h14 | h14
        · rcases m.htr 0 2 5 (by decide) (by decide) with h15 | h15
          · linarith only [h15, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi7]
          · linarith only [h14, h15, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h18 | h18
          · linarith only [h18, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi7]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h20 | h20
            · linarith only [h20, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi9]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
              · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h0, h14, h20, h22, h25, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h14, h24, h25, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h24, h8, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h23, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h18, h22, h30, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h30, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem n7l_sBT2_H_L_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2ehi := hb2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi9]
    · linarith only [h0, h2, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo4]

theorem n7l_sBT2_H_R_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  linarith only [hlam, hphi, ht01, ht12, u0ehi1, u2elo0]

theorem n7l_sBT2_H_R_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h5bigk := hb5.1
  have h2ehi := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                                    · linarith only [h0, h14, h17, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h0, h14, h16, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h12, h13, h16, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                                  · linarith only [h14, h15, h21, hlam]
                                  · linarith only [h0, h12, h13, h21, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h0, h12, h14, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                                  · linarith only [h0, h13, h25, h27, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                                    · linarith only [h10, h13, h29, hc34, hlam, hphi, ht23, u2ehi3]
                                    · rcases h5bigk with h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [hlam, p31_0]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h0, h11, h27, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi3]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h0, h27, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi3]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        rcases p31_3 (m.d 0 5) (by simp) with h35 | h35
                                        · rcases p31_3 (m.d 1 5) (by simp) with h36 | h36
                                          · linarith only [h2, h36, hlam]
                                          · linarith only [h0, h11, h27, h3, h36, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi3]
                                        · linarith only [h35, h7, hlam]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h0, h10, h13, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi3]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h2, hlam, p31_0]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [hlam, p31_0]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h27, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi3]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h13, h29, hc34, hc45, hlam, hphi, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h13, hlam, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h5, hlam, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h11, hlam, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [hlam, p31_0]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h0, h29, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h27, hlam, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h7, hlam, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h26, hlam, p31_0]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [hlam, p31_0]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h29, hlam, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h8, hlam, p31_0]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h0, h3, h6, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h0, h3, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [h0, h3, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p31_1]
                                      · have p31_0 := h31c.1
                                        have p31_1 := h31c.2.1
                                        have p31_2 := h31c.2.2.1
                                        have p31_3 := h31c.2.2.2
                                        linarith only [hlam, p31_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                                  · linarith only [h10, h13, h61, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                                    · linarith only [h10, h13, h63, hc34, hlam, hphi, ht23, u2ehi3]
                                    · rcases h5bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h11, h25, h26, h3, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h26, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1, u2ehi2]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h25, h26, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1, u2ehi3]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h10, h13, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1, u2ehi3]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h2, hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h25, h26, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p65_1, u2ehi3]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h25, h26, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p65_1, u2ehi3]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h13, hlam, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h5, hlam, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h11, hlam, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h26, hlam, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h61, hlam, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h7, hlam, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h25, h26, h3, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1, u2ehi3]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h63, hlam, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h8, hlam, p65_0]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h11, h25, h26, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1, u2ehi3]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h25, h26, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1, u2ehi3]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [h0, h3, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p65_1]
                                      · have p65_0 := h65c.1
                                        have p65_1 := h65c.2.1
                                        have p65_2 := h65c.2.2.1
                                        have p65_3 := h65c.2.2.2
                                        linarith only [hlam, p65_0]
                              · linarith only [h0, h12, h25, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                              · linarith only [h12, h9, h93, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
                                    · rcases h5bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [hlam, p98_0]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h0, h11, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi4]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi4]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        rcases p98_3 (m.d 0 5) (by simp) with h102 | h102
                                        · rcases p98_3 (m.d 1 5) (by simp) with h103 | h103
                                          · linarith only [h103, h2, hlam]
                                          · linarith only [h103, h11, h12, h9, h95, hc34, hlam, hphi, ht23, u2ehi4]
                                        · linarith only [h102, h7, hlam]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        rcases p98_3 (m.d 0 5) (by simp) with h107 | h107
                                        · rcases p98_3 (m.d 1 5) (by simp) with h108 | h108
                                          · linarith only [h108, h2, hlam]
                                          · linarith only [h108, h92, hlam]
                                        · linarith only [h107, h8, hlam]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h2, hlam, p98_0]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [hlam, p98_0]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi4]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h1, h92, hc01, hc35, hlam, hphi, ht0b, ht5b, p98_1]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h0, h12, h3, h6, h92, hc01, hc45, hlam, hphi, ht0b, ht5b, p98_1]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h5, hlam, p98_1]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h11, hlam, p98_1]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [hlam, p98_0]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h0, h5, h97, hc01, hc45, hlam, hphi, ht0b, ht5b, p98_1]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h0, h12, h3, h6, h9, h95, hc01, hc45, hlam, hphi, ht0b, ht5b, p98_1]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h7, hlam, p98_1]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p98_1]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h95, hlam, p98_0]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [hlam, p98_0]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h0, h12, h3, h6, h9, h95, hc01, hc45, hlam, hphi, ht0b, ht5b, p98_1]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h8, hlam, p98_0]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h92, hlam, p98_0]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h96, hlam, p98_0]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [h97, hlam, p98_0]
                                      · have p98_0 := h98c.1
                                        have p98_1 := h98c.2.1
                                        have p98_2 := h98c.2.2.1
                                        have p98_3 := h98c.2.2.2
                                        linarith only [hlam, p98_0]
                                    · linarith only [h12, h9, h95, h97, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                  · linarith only [h12, h92, h93, h95, h96, hc34, hlam, hphi, ht23, u2ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                                    · rcases h5bigk with h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h11, h8, h95, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p136_1, u2ehi2]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h0, h4, h8, h95, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p136_1, u2ehi2]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h0, h3, h6, h8, h95, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p136_1, u2ehi2]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        rcases p136_3 (m.d 0 5) (by simp) with h141 | h141
                                        · rcases p136_3 (m.d 1 5) (by simp) with h142 | h142
                                          · linarith only [h142, h2, hlam]
                                          · linarith only [h142, h92, hlam]
                                        · linarith only [h141, h8, hlam]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h2, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h95, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p136_1, u2ehi2]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h92, h95, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p136_1, u2ehi2]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h0, h12, h3, h6, h92, hc01, hc45, hlam, hphi, ht0b, ht5b, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h5, hlam, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h11, hlam, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h95, hlam, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h0, h134, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h7, hlam, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h0, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h0, h135, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h8, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h92, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h134, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h135, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [hlam, p136_0]
                                    · linarith only [h0, h12, h135, h3, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · linarith only [h1, h134, h92, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                              · linarith only [h12, h168, h9, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h171 | h171
                                  · linarith only [h0, h10, h171, h92, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h168, h170, h171, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h174 | h174
                                  · linarith only [h12, h174, h9, h92, hc24, hlam, hphi, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h176 | h176
                                    · linarith only [h12, h176, h9, h92, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h0, h12, h176, h3, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h11, h5, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h9, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                      · linarith only [h181, h9, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                        · linarith only [h0, h183, h3, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h186 | h186
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h188 | h188
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h189 | h189
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h190 | h190
                                    · rcases h5bigk with h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h0, h183, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p191_1, u2ehi1]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p191_1, u2ehi4]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        rcases p191_3 (m.d 0 5) (by simp) with h195 | h195
                                        · rcases p191_3 (m.d 1 5) (by simp) with h196 | h196
                                          · linarith only [h196, h2, hlam]
                                          · linarith only [h0, h183, h196, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p191_1, u2ehi1]
                                        · linarith only [h195, h7, hlam]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        rcases p191_3 (m.d 0 5) (by simp) with h200 | h200
                                        · rcases p191_3 (m.d 1 5) (by simp) with h201 | h201
                                          · linarith only [h2, h201, hlam]
                                          · linarith only [h186, h201, hlam]
                                        · linarith only [h200, h8, hlam]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h2, hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h183, hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h1, h186, hc01, hc35, hlam, hphi, ht0b, ht5b, p191_1]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p191_1]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h5, hlam, p191_1]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p191_1]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h0, h188, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p191_1]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h0, h187, h189, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p191_1]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h7, hlam, p191_1]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h183, hc35, hlam, hphi, ht23, p191_1, u2ehi1]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h188, hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h0, h190, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p191_1]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h8, hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h186, hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h189, hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [h190, hlam, p191_0]
                                      · have p191_0 := h191c.1
                                        have p191_1 := h191c.2.1
                                        have p191_2 := h191c.2.2.1
                                        have p191_3 := h191c.2.2.2
                                        linarith only [hlam, p191_0]
                                    · rcases h5bigk with h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [hlam, p225_0]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h0, h186, h190, h3, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p225_1, u2ehi4]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        rcases p225_3 (m.d 0 5) (by simp) with h229 | h229
                                        · rcases p225_3 (m.d 1 5) (by simp) with h230 | h230
                                          · linarith only [h2, h230, hlam]
                                          · linarith only [h0, h183, h230, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p225_1, u2ehi1]
                                        · linarith only [h229, h7, hlam]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h0, h190, h3, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h2, hlam, p225_0]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [hlam, p225_0]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h183, hlam, p225_0]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h190, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h5, hlam, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [hlam, p225_0]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h0, h188, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h0, h187, h189, h190, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h7, hlam, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h183, hc35, hlam, hphi, ht23, p225_1, u2ehi1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h188, hlam, p225_0]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [hlam, p225_0]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h190, hlam, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h8, hlam, p225_0]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h186, hlam, p225_0]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h189, hlam, p225_0]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [h0, h3, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p225_1]
                                      · have p225_0 := h225c.1
                                        have p225_1 := h225c.2.1
                                        have p225_2 := h225c.2.2.1
                                        have p225_3 := h225c.2.2.2
                                        linarith only [hlam, p225_0]
                                  · linarith only [h0, h181, h189, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h188, h3, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h0, h187, h3, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h258 | h258
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
                                  · linarith only [h0, h181, h186, h260, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h0, h181, h260, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h259, h3, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h185, h258, h9, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h265 | h265
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h266 | h266
                              · linarith only [h185, h266, h9, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h266, h3, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                              · linarith only [h185, h269, h9, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h269, h3, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · linarith only [h8, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                · linarith only [h7, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
              · linarith only [h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc25, hlam, hphi, ht01, ht12, u0ehi1]
          · linarith only [h3, h4, hc24, hlam, hphi, ht01, ht12, u0ehi2]
        · linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc15, hlam, hphi, ht01, u0ehi0]
    · linarith only [h0, h1, hc14, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT2_H_R_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_H_R_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_H_R_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_H_R_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  linarith only [hlam, hphi, ht01, ht12, u0ehi1, u2elo0]

theorem n7l_sBT2_H_R_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0ehi := hb0.1
  have h5ehi := hb5.1
  have h2bigk := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                      · linarith only [h0, h11, h3, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h0, h11, h13, h3, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h1, h13, h15, h5, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                            · linarith only [h11, h15, h17, h8, h9, hc23, hc34, hlam, hphi]
                            · rcases h2bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                rcases p19_3 (m.d 0 2) (by simp) with h21 | h21
                                · rcases p19_3 (m.d 1 2) (by simp) with h22 | h22
                                  · linarith only [h0, h22, hlam]
                                  · rcases p19_3 (m.d 2 3) (by simp) with h24 | h24
                                    · linarith only [h1, h24, hlam]
                                    · rcases p19_3 (m.d 2 4) (by simp) with h26 | h26
                                      · linarith only [h2, h26, hlam]
                                      · rcases p19_3 (m.d 2 5) (by simp) with h28 | h28
                                        · linarith only [h28, h3, hlam]
                                        · linarith only [h28, h9, hlam]
                                · linarith only [h0, h21, hlam]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h1, h11, h13, h17, h4, h6, h8, h9, hlam, p19_2]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h1, h13, h17, h4, h6, h8, h9, hlam, p19_2]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h0, h11, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h0, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h0, h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h0, h11, h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h9, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h1, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h7, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h11, hlam, p19_1]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h13, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h2, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h8, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h0, h3, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h15, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h3, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h0, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                rcases p19_3 (m.d 0 2) (by simp) with h52 | h52
                                · rcases p19_3 (m.d 1 2) (by simp) with h53 | h53
                                  · linarith only [h53, h9, hlam]
                                  · linarith only [h53, h7, hlam]
                                · linarith only [h1, h52, hlam]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                rcases p19_3 (m.d 0 2) (by simp) with h57 | h57
                                · rcases p19_3 (m.d 1 2) (by simp) with h58 | h58
                                  · linarith only [h58, h9, hlam]
                                  · linarith only [h58, h8, hlam]
                                · linarith only [h2, h57, hlam]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hlam, p19_0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                    · linarith only [h63, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                      · linarith only [h0, h2, h65, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                        · linarith only [h0, h1, h4, h65, h67, h7, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                          · linarith only [h0, h1, h4, h65, h69, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h69, h7, h8, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                    · linarith only [h7, h73, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h76 | h76
                        · linarith only [h0, h1, h76, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h1, h5, h7, h72, h75, h76, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h4, h7, h72, h75, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h7, h80, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                        · linarith only [h0, h1, h83, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                          · linarith only [h0, h1, h5, h82, h83, h85, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                            · linarith only [h0, h1, h5, h72, h82, h83, h85, h87, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases h2bigk with h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h1, h4, h6, h7, h83, h87, hlam, p89_2]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                rcases p89_3 (m.d 0 2) (by simp) with h92 | h92
                                · rcases p89_3 (m.d 1 2) (by simp) with h93 | h93
                                  · linarith only [h0, h93, hlam]
                                  · rcases p89_3 (m.d 2 3) (by simp) with h95 | h95
                                    · linarith only [h95, hlam, p89_0]
                                    · rcases p89_3 (m.d 2 4) (by simp) with h97 | h97
                                      · linarith only [h2, h97, hlam]
                                      · rcases p89_3 (m.d 2 5) (by simp) with h99 | h99
                                        · linarith only [h3, h99, hlam]
                                        · linarith only [h83, h99, hlam]
                                · linarith only [h92, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                rcases p89_3 (m.d 0 2) (by simp) with h103 | h103
                                · rcases p89_3 (m.d 1 2) (by simp) with h104 | h104
                                  · linarith only [h0, h104, hlam]
                                  · rcases p89_3 (m.d 2 3) (by simp) with h106 | h106
                                    · linarith only [h1, h106, hlam]
                                    · linarith only [h106, h82, hlam]
                                · linarith only [h103, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h0, h80, hc01, hlam, hphi, ht0b, ht5b, p89_1, u5ehi1]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h0, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h7, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h72, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h80, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h1, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h0, h1, h4, h6, h83, h87, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p89_1]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h0, h1, h4, h6, h72, h83, h87, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p89_1]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h83, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h2, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h0, h1, h4, h6, h82, h83, h87, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p89_1]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h82, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h85, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h3, hlam, p89_0]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                rcases p89_3 (m.d 0 2) (by simp) with h127 | h127
                                · rcases p89_3 (m.d 1 2) (by simp) with h128 | h128
                                  · linarith only [h128, hlam, p89_0]
                                  · rcases p89_3 (m.d 2 3) (by simp) with h130 | h130
                                    · linarith only [h130, h83, hlam]
                                    · linarith only [h130, h7, hlam]
                                · linarith only [h0, h127, hlam]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h0, h3, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p89_1]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [h0, h1, h4, h6, h72, h83, h87, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p89_1]
                              · have p89_0 := h89c.1
                                have p89_1 := h89c.2.1
                                have p89_2 := h89c.2.2.1
                                have p89_3 := h89c.2.2.2
                                linarith only [hlam, p89_0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h137 | h137
                        · linarith only [h137, h82, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
                          · linarith only [h0, h139, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                            · linarith only [h0, h1, h139, h141, h4, h7, h82, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h141, h7, h82, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
            · linarith only [h5, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc25, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h1, h2, hc24, hlam, hphi, ht01, ht12, u0ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht01, ht12, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT2_H_R_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5ehi := hb5.1
  have h2ehi := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
        · linarith only [h2, h3, hc25, hlam, hphi, u2ehi3]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
        · linarith only [h2, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
          · linarith only [h0, h1, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · linarith only [h2, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · linarith only [h1, hc24, hlam, hphi, ht01, ht12, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT2_H_R_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  linarith only [hlam, hphi, ht01, ht12, u0ehi1, u2elo0]

theorem n7l_sBT2_H_R_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h2ehi := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h0, h12, h13, h14, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h13, h17, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h0, h12, h17, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                              · linarith only [h0, h12, h21, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                                · linarith only [h0, h12, h20, h23, h3, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                                  · linarith only [h23, h25, hc34, hlam, hphi, ht23, u2ehi3]
                                  · rcases h5bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      rcases p27_3 (m.d 0 5) (by simp) with h29 | h29
                                      · rcases p27_3 (m.d 1 5) (by simp) with h30 | h30
                                        · linarith only [h2, h30, hlam]
                                        · rcases p27_3 (m.d 2 5) (by simp) with h32 | h32
                                          · linarith only [h32, h5, hlam]
                                          · rcases p27_3 (m.d 3 5) (by simp) with h34 | h34
                                            · linarith only [h34, h7, hlam]
                                            · linarith only [h12, h34, hlam]
                                      · linarith only [h2, h29, hlam]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      rcases p27_3 (m.d 0 5) (by simp) with h38 | h38
                                      · rcases p27_3 (m.d 1 5) (by simp) with h39 | h39
                                        · linarith only [h2, h39, hlam]
                                        · linarith only [h11, h39, hlam]
                                      · linarith only [h38, h5, hlam]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, h12, h20, h3, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, h23, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h2, hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi4]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h12, hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h12, h25, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h5, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h11, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h21, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h23, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h7, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, h3, h7, hc01, hlam, hphi, ht0b, ht5b, p27_1, u5ehi1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, h20, h21, h25, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h25, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h8, hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, h11, h20, h21, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, h20, h21, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, p27_1, u5ehi3]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hlam, p27_0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                              · linarith only [h12, h65, h9, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h67 | h67
                                · linarith only [h0, h10, h67, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
                                  · linarith only [h0, h20, h3, h6, h67, h69, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · linarith only [h20, h69, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h11, h5, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h9, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                      · linarith only [h74, h9, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                        · linarith only [h0, h3, h76, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
                                  · linarith only [h0, h3, h79, h82, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h5bigk with h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [hlam, p84_0]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      rcases p84_3 (m.d 0 5) (by simp) with h86 | h86
                                      · rcases p84_3 (m.d 1 5) (by simp) with h87 | h87
                                        · linarith only [h2, h87, hlam]
                                        · rcases p84_3 (m.d 2 5) (by simp) with h89 | h89
                                          · linarith only [h5, h89, hlam]
                                          · linarith only [h76, h89, hlam]
                                      · linarith only [h2, h86, hlam]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h0, h3, h6, h76, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p84_1, u2ehi1]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      rcases p84_3 (m.d 0 5) (by simp) with h94 | h94
                                      · rcases p84_3 (m.d 1 5) (by simp) with h95 | h95
                                        · linarith only [h2, h95, hlam]
                                        · linarith only [h78, h95, hlam]
                                      · linarith only [h7, h94, hlam]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      rcases p84_3 (m.d 0 5) (by simp) with h99 | h99
                                      · rcases p84_3 (m.d 1 5) (by simp) with h100 | h100
                                        · linarith only [h100, h2, hlam]
                                        · rcases p84_3 (m.d 2 5) (by simp) with h102 | h102
                                          · linarith only [h102, h5, hlam]
                                          · linarith only [h102, h81, hlam]
                                      · linarith only [h8, h99, hlam]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h2, hlam, p84_0]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [hlam, p84_0]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h76, hlam, p84_0]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p84_1, u5ehi3]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h1, h78, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p84_1]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h5, hlam, p84_1]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht5b, p84_1, u5ehi1]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [hlam, p84_0]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h0, h3, h80, hc01, hlam, hphi, ht0b, ht5b, p84_1, u5ehi3]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h0, h3, h79, h81, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p84_1]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h7, hlam, p84_1]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h78, hlam, p84_1]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h80, hlam, p84_0]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [hlam, p84_0]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h82, hlam, p84_1]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h8, hlam, p84_0]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h76, hc45, hlam, hphi, ht23, ht34, p84_1, u2ehi1]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h81, hlam, p84_0]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [h0, h3, h79, h81, hc01, hlam, hphi, ht0b, ht5b, p84_1, u5ehi3]
                                    · have p84_0 := h84c.1
                                      have p84_1 := h84c.2.1
                                      have p84_2 := h84c.2.2.1
                                      have p84_3 := h84c.2.2.2
                                      linarith only [hlam, p84_0]
                                · linarith only [h0, h3, h6, h74, h8, h81, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h0, h3, h7, h80, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h79, h9, hc34, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h129 | h129
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h130 | h130
                              · linarith only [h130, h78, h9, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h130, h3, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h129, h9, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h8, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                · linarith only [h7, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
              · linarith only [h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc25, hlam, hphi, ht01, ht12, u0ehi1]
          · linarith only [h3, h4, hc24, hlam, hphi, ht01, ht12, u0ehi2]
        · linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc15, hlam, hphi, ht01, u0ehi0]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT2_H_R_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_H_R_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_H_R_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_H_R_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_H_R_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_H_R_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_M_IR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi2, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi3, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi4, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_M_IR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_M_IR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT2_M_IR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5ehi := hb5.1
  have h2elo := hb2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]

theorem n7l_sBT2_M_IR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi2, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi3, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi4, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have h2elo := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi2, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi3, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi4, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi2, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h2ehi := hb2.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht23, ht34, ht45, p0_1, u2ehi4, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht23, ht34, ht45, p0_1, u2ehi4, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have h2elo := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi2, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi3, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi4, u2elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi2, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi2, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_IR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi2, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LI_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5bigk := hb5.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 5) (by simp) with h9 | h9
        · linarith only [h9, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h11 | h11
          · rcases p0_3 (m.d 4 5) (by simp) with h12 | h12
            · rcases m.htr 0 1 2 (by decide) (by decide) with h13 | h13
              · rcases m.htr 0 1 5 (by decide) (by decide) with h14 | h14
                · linarith only [h14, hlam, p0_0]
                · linarith only [h12, h14, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h17 | h17
                · linarith only [h17, hlam, p0_0]
                · linarith only [h12, h17, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h20 | h20
              · rcases m.htr 0 1 5 (by decide) (by decide) with h21 | h21
                · linarith only [h21, hlam, p0_0]
                · linarith only [h20, h21, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h24 | h24
                · linarith only [h24, hlam, p0_0]
                · linarith only [h11, h24, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h27 | h27
            · rcases m.htr 0 1 2 (by decide) (by decide) with h28 | h28
              · rcases m.htr 0 1 5 (by decide) (by decide) with h29 | h29
                · linarith only [h29, hlam, p0_0]
                · linarith only [h27, h29, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h32 | h32
                · linarith only [h32, hlam, p0_0]
                · linarith only [h27, h32, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h35 | h35
              · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
                · linarith only [h36, hlam, p0_0]
                · linarith only [h35, h36, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h39 | h39
                · linarith only [h39, hlam, p0_0]
                · linarith only [h39, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h8, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h44 | h44
    · linarith only [h44, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h46 | h46
      · rcases p0_3 (m.d 2 5) (by simp) with h47 | h47
        · linarith only [h47, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h49 | h49
          · rcases p0_3 (m.d 4 5) (by simp) with h50 | h50
            · rcases m.htr 0 1 2 (by decide) (by decide) with h51 | h51
              · rcases m.htr 0 1 5 (by decide) (by decide) with h52 | h52
                · linarith only [h52, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h44, h51, h52, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h55 | h55
                · linarith only [h44, h55, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h44, h55, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h58 | h58
              · rcases m.htr 0 1 5 (by decide) (by decide) with h59 | h59
                · linarith only [h44, h59, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h44, h49, h59, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h62 | h62
                · linarith only [h44, h58, h62, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h44, h62, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h65 | h65
            · rcases m.htr 0 1 2 (by decide) (by decide) with h66 | h66
              · rcases m.htr 0 1 5 (by decide) (by decide) with h67 | h67
                · linarith only [h44, h67, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h44, h65, h67, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h70 | h70
                · linarith only [h44, h66, h70, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h44, h70, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h73 | h73
              · rcases m.htr 0 1 5 (by decide) (by decide) with h74 | h74
                · linarith only [h44, h74, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h44, h73, h74, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h77 | h77
                · linarith only [h44, h77, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h44, h77, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h46, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h81 | h81
    · linarith only [h81, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h83 | h83
      · rcases p0_3 (m.d 2 5) (by simp) with h84 | h84
        · linarith only [h84, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h88 | h88
            · rcases m.htr 0 1 2 (by decide) (by decide) with h89 | h89
              · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
                · linarith only [h90, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h81, h88, h90, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h93 | h93
                · linarith only [h81, h89, h93, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h81, h93, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h96 | h96
              · rcases m.htr 0 1 5 (by decide) (by decide) with h97 | h97
                · linarith only [h81, h97, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h81, h96, h97, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h100 | h100
                · linarith only [h100, h81, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h100, h81, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h83, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
    · linarith only [h104, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h106 | h106
      · rcases p0_3 (m.d 2 5) (by simp) with h107 | h107
        · linarith only [h107, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h109 | h109
          · rcases p0_3 (m.d 4 5) (by simp) with h110 | h110
            · linarith only [h110, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 1 5 (by decide) (by decide) with h113 | h113
                · linarith only [h113, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h104, h109, h113, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h116 | h116
                · linarith only [h104, h112, h116, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h104, h116, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h121 | h121
              · rcases m.htr 0 1 5 (by decide) (by decide) with h122 | h122
                · linarith only [h104, h122, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h104, h121, h122, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h125 | h125
                · linarith only [h104, h125, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h104, h125, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h106, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
    · linarith only [h134, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h136 | h136
      · rcases p0_3 (m.d 2 5) (by simp) with h137 | h137
        · linarith only [h137, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h139 | h139
          · rcases p0_3 (m.d 4 5) (by simp) with h140 | h140
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · rcases m.htr 0 1 5 (by decide) (by decide) with h142 | h142
                · linarith only [h136, h142, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h141, h142, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h145 | h145
                · linarith only [h136, h145, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h136, h145, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h148 | h148
              · rcases m.htr 0 1 5 (by decide) (by decide) with h149 | h149
                · linarith only [h136, h149, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h148, h149, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h152 | h152
                · linarith only [h136, h152, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h136, h152, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h139, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h156 | h156
        · linarith only [h156, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h158 | h158
          · rcases p0_3 (m.d 4 5) (by simp) with h159 | h159
            · rcases m.htr 0 1 2 (by decide) (by decide) with h160 | h160
              · rcases m.htr 0 1 5 (by decide) (by decide) with h161 | h161
                · rcases m.htr 0 2 5 (by decide) (by decide) with h162 | h162
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
                    · linarith only [h163, hlam, p0_0]
                    · linarith only [h163, hc03, hc35, hlam, hphi, p0_1]
                  · linarith only [h156, h162, hlam]
                · linarith only [h136, h161, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h168 | h168
                · rcases m.htr 0 2 5 (by decide) (by decide) with h169 | h169
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
                    · linarith only [h170, hlam, p0_0]
                    · linarith only [h159, h170, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h156, h169, hlam]
                · linarith only [h136, h168, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h175 | h175
              · rcases m.htr 0 1 5 (by decide) (by decide) with h176 | h176
                · rcases m.htr 0 2 5 (by decide) (by decide) with h177 | h177
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h178 | h178
                    · linarith only [h178, hlam, p0_0]
                    · linarith only [h178, hc03, hc35, hlam, hphi, p0_1]
                  · linarith only [h156, h177, hlam]
                · linarith only [h136, h176, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h183 | h183
                · rcases m.htr 0 2 5 (by decide) (by decide) with h184 | h184
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h185 | h185
                    · linarith only [h185, hlam, p0_0]
                    · linarith only [h185, hc03, hc35, hlam, hphi, p0_1]
                  · linarith only [h156, h184, hlam]
                · linarith only [h136, h183, hlam]
          · linarith only [h158, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h191 | h191
    · linarith only [h191, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h193 | h193
      · linarith only [h193, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h195 | h195
        · linarith only [h195, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h197 | h197
          · rcases p0_3 (m.d 4 5) (by simp) with h198 | h198
            · rcases m.htr 0 1 2 (by decide) (by decide) with h199 | h199
              · rcases m.htr 0 1 5 (by decide) (by decide) with h200 | h200
                · linarith only [h191, h200, hlam]
                · linarith only [h198, h200, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h203 | h203
                · linarith only [h191, h203, hlam]
                · linarith only [h198, h203, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h206 | h206
              · rcases m.htr 0 1 5 (by decide) (by decide) with h207 | h207
                · linarith only [h191, h207, hlam]
                · linarith only [h206, h207, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h210 | h210
                · linarith only [h191, h210, hlam]
                · linarith only [h210, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h197, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h214 | h214
    · linarith only [h214, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h216 | h216
      · rcases p0_3 (m.d 2 5) (by simp) with h217 | h217
        · linarith only [h217, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h219 | h219
          · rcases p0_3 (m.d 4 5) (by simp) with h220 | h220
            · rcases m.htr 0 1 2 (by decide) (by decide) with h221 | h221
              · rcases m.htr 0 1 5 (by decide) (by decide) with h222 | h222
                · linarith only [h216, h222, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h214, h221, h222, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h225 | h225
                · linarith only [h214, h216, h225, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h214, h216, h225, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h228 | h228
              · rcases m.htr 0 1 5 (by decide) (by decide) with h229 | h229
                · linarith only [h214, h216, h229, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h214, h228, h229, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h232 | h232
                · linarith only [h214, h216, h232, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h214, h216, h232, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h219, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h236 | h236
        · linarith only [h236, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h238 | h238
          · rcases p0_3 (m.d 4 5) (by simp) with h239 | h239
            · rcases m.htr 0 1 2 (by decide) (by decide) with h240 | h240
              · rcases m.htr 0 1 5 (by decide) (by decide) with h241 | h241
                · rcases m.htr 0 2 5 (by decide) (by decide) with h242 | h242
                  · linarith only [h214, h242, hlam]
                  · linarith only [h239, h242, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h216, h239, h241, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h246 | h246
                · rcases m.htr 0 2 5 (by decide) (by decide) with h247 | h247
                  · linarith only [h214, h247, hlam]
                  · linarith only [h239, h240, h246, h247, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                · linarith only [h216, h239, h246, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h251 | h251
              · rcases m.htr 0 1 5 (by decide) (by decide) with h252 | h252
                · rcases m.htr 0 2 5 (by decide) (by decide) with h253 | h253
                  · linarith only [h214, h253, hlam]
                  · linarith only [h251, h253, hc12, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h216, h251, h252, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h257 | h257
                · rcases m.htr 0 2 5 (by decide) (by decide) with h258 | h258
                  · linarith only [h214, h258, hlam]
                  · linarith only [h251, h257, h258, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1]
                · linarith only [h216, h257, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h238, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h264 | h264
    · linarith only [h264, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h266 | h266
      · rcases p0_3 (m.d 2 5) (by simp) with h267 | h267
        · linarith only [h267, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h269 | h269
          · rcases p0_3 (m.d 4 5) (by simp) with h270 | h270
            · linarith only [h270, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h272 | h272
              · rcases m.htr 0 1 5 (by decide) (by decide) with h273 | h273
                · linarith only [h266, h273, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h264, h273, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h276 | h276
                · linarith only [h264, h266, h276, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h264, h266, h276, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h269, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h280 | h280
        · linarith only [h264, h280, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h282 | h282
          · rcases p0_3 (m.d 4 5) (by simp) with h283 | h283
            · linarith only [h283, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h285 | h285
              · rcases m.htr 0 1 5 (by decide) (by decide) with h286 | h286
                · rcases m.htr 0 2 5 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h288 | h288
                    · linarith only [h264, h286, h288, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h264, h288, hc03, hc35, hlam, hphi, p0_1]
                  · linarith only [h280, h287, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h266, h286, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h293 | h293
                · rcases m.htr 0 2 5 (by decide) (by decide) with h294 | h294
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h295 | h295
                    · linarith only [h264, h295, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h264, h295, hc03, hc35, hlam, hphi, p0_1]
                  · linarith only [h280, h285, h293, h294, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1]
                · linarith only [h266, h293, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h282, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h301 | h301
    · linarith only [h301, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h303 | h303
      · rcases p0_3 (m.d 2 5) (by simp) with h304 | h304
        · linarith only [h304, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h306 | h306
          · rcases p0_3 (m.d 4 5) (by simp) with h307 | h307
            · rcases m.htr 0 1 2 (by decide) (by decide) with h308 | h308
              · rcases m.htr 0 1 5 (by decide) (by decide) with h309 | h309
                · linarith only [h303, h309, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h309, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h312 | h312
                · linarith only [h303, h312, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h303, h312, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h307, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h316 | h316
            · rcases m.htr 0 1 2 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 1 5 (by decide) (by decide) with h318 | h318
                · linarith only [h303, h318, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h317, h318, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h321 | h321
                · linarith only [h303, h321, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h303, h321, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h316, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h325 | h325
        · linarith only [h325, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h327 | h327
          · rcases p0_3 (m.d 4 5) (by simp) with h328 | h328
            · rcases m.htr 0 1 2 (by decide) (by decide) with h329 | h329
              · rcases m.htr 0 1 5 (by decide) (by decide) with h330 | h330
                · rcases m.htr 0 2 5 (by decide) (by decide) with h331 | h331
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h332 | h332
                    · linarith only [h327, h330, h332, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h327, h332, hc03, hc35, hlam, hphi, p0_1]
                  · linarith only [h325, h331, hlam]
                · linarith only [h303, h330, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h337 | h337
                · rcases m.htr 0 2 5 (by decide) (by decide) with h338 | h338
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h339 | h339
                    · linarith only [h327, h339, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h339, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h325, h338, hlam]
                · linarith only [h303, h337, hlam]
            · linarith only [h328, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h345 | h345
            · rcases m.htr 0 1 2 (by decide) (by decide) with h346 | h346
              · rcases m.htr 0 1 5 (by decide) (by decide) with h347 | h347
                · rcases m.htr 0 2 5 (by decide) (by decide) with h348 | h348
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h349 | h349
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h350 | h350
                      · linarith only [h350, hlam, p0_0]
                      · linarith only [h350, hc04, hc45, hlam, hphi, p0_1]
                    · linarith only [h327, h349, hlam]
                  · linarith only [h325, h348, hlam]
                · linarith only [h303, h347, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h356 | h356
                · rcases m.htr 0 2 5 (by decide) (by decide) with h357 | h357
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h358 | h358
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h359 | h359
                      · linarith only [h359, hlam, p0_0]
                      · linarith only [h359, hc04, hc45, hlam, hphi, p0_1]
                    · linarith only [h327, h358, hlam]
                  · linarith only [h325, h357, hlam]
                · linarith only [h303, h356, hlam]
            · linarith only [h345, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h366 | h366
    · linarith only [h366, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h368 | h368
      · linarith only [h368, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h370 | h370
        · linarith only [h370, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h372 | h372
          · rcases p0_3 (m.d 4 5) (by simp) with h373 | h373
            · rcases m.htr 0 1 2 (by decide) (by decide) with h374 | h374
              · rcases m.htr 0 1 5 (by decide) (by decide) with h375 | h375
                · linarith only [h366, h375, hlam]
                · linarith only [h372, h374, h375, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h378 | h378
                · linarith only [h366, h378, hlam]
                · linarith only [h378, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h373, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h382 | h382
            · rcases m.htr 0 1 2 (by decide) (by decide) with h383 | h383
              · rcases m.htr 0 1 5 (by decide) (by decide) with h384 | h384
                · linarith only [h366, h384, hlam]
                · linarith only [h384, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h387 | h387
                · linarith only [h366, h387, hlam]
                · linarith only [h387, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h382, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h391 | h391
    · linarith only [h391, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h393 | h393
      · rcases p0_3 (m.d 2 5) (by simp) with h394 | h394
        · linarith only [h394, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h396 | h396
          · rcases p0_3 (m.d 4 5) (by simp) with h397 | h397
            · rcases m.htr 0 1 2 (by decide) (by decide) with h398 | h398
              · rcases m.htr 0 1 5 (by decide) (by decide) with h399 | h399
                · linarith only [h393, h399, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h391, h396, h398, h399, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h402 | h402
                · linarith only [h391, h393, h402, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h391, h393, h402, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h397, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h406 | h406
            · rcases m.htr 0 1 2 (by decide) (by decide) with h407 | h407
              · rcases m.htr 0 1 5 (by decide) (by decide) with h408 | h408
                · linarith only [h391, h393, h408, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h391, h407, h408, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h411 | h411
                · linarith only [h391, h393, h411, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h391, h393, h411, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h406, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h415 | h415
        · linarith only [h415, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h417 | h417
          · rcases p0_3 (m.d 4 5) (by simp) with h418 | h418
            · rcases m.htr 0 1 2 (by decide) (by decide) with h419 | h419
              · rcases m.htr 0 1 5 (by decide) (by decide) with h420 | h420
                · rcases m.htr 0 2 5 (by decide) (by decide) with h421 | h421
                  · linarith only [h391, h421, hlam]
                  · linarith only [h421, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h393, h419, h420, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h425 | h425
                · rcases m.htr 0 2 5 (by decide) (by decide) with h426 | h426
                  · linarith only [h391, h426, hlam]
                  · linarith only [h419, h425, h426, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                · linarith only [h393, h425, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h418, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h431 | h431
            · rcases m.htr 0 1 2 (by decide) (by decide) with h432 | h432
              · rcases m.htr 0 1 5 (by decide) (by decide) with h433 | h433
                · rcases m.htr 0 2 5 (by decide) (by decide) with h434 | h434
                  · linarith only [h391, h434, hlam]
                  · linarith only [h434, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h393, h432, h433, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h438 | h438
                · rcases m.htr 0 2 5 (by decide) (by decide) with h439 | h439
                  · linarith only [h391, h439, hlam]
                  · linarith only [h432, h438, h439, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                · linarith only [h393, h438, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h431, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h444 | h444
    · linarith only [h444, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h446 | h446
      · rcases p0_3 (m.d 2 5) (by simp) with h447 | h447
        · linarith only [h447, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h449 | h449
          · linarith only [h449, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h451 | h451
            · rcases m.htr 0 1 2 (by decide) (by decide) with h452 | h452
              · rcases m.htr 0 1 5 (by decide) (by decide) with h453 | h453
                · linarith only [h446, h453, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h444, h453, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h456 | h456
                · linarith only [h444, h446, h456, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h444, h446, h456, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h451, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h460 | h460
        · linarith only [h444, h460, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
        · rcases p0_3 (m.d 3 5) (by simp) with h462 | h462
          · linarith only [h462, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h464 | h464
            · rcases m.htr 0 1 2 (by decide) (by decide) with h465 | h465
              · rcases m.htr 0 1 5 (by decide) (by decide) with h466 | h466
                · rcases m.htr 0 2 5 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h468 | h468
                    · linarith only [h444, h468, hlam]
                    · linarith only [h468, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h460, h467, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h446, h466, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h473 | h473
                · rcases m.htr 0 2 5 (by decide) (by decide) with h474 | h474
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h475 | h475
                    · linarith only [h444, h475, hlam]
                    · linarith only [h475, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h460, h465, h473, h474, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                · linarith only [h446, h473, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h464, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LI_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h5elo := hb5.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h10, h12, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h11, hc14, hlam, hphi, ht45, u5elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                          · linarith only [h10, h17, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                            · linarith only [h10, h19, h3, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h19, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h16, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
                · linarith only [h7, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                      · linarith only [h1, h29, h6, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                          · linarith only [h1, h27, h32, h6, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                            · linarith only [h0, h27, h34, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h34, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h29, h31, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h28, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h27, h3, hc12, hlam, hphi, u2elo0]
                · linarith only [h26, h6, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h3, h5, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h42 | h42
            · rcases m.htr 0 3 4 (by decide) (by decide) with h43 | h43
              · linarith only [h3, h4, h43, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h45 | h45
                · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                      · linarith only [h1, h43, h48, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                          · linarith only [h0, h4, h43, h46, h51, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                            · linarith only [h3, h4, h53, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                            · linarith only [h53, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h50, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h47, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h3, h4, h46, hc12, hlam, hphi, u2elo3]
                · linarith only [h45, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h42, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h61 | h61
          · rcases m.htr 0 2 5 (by decide) (by decide) with h62 | h62
            · rcases m.htr 0 3 4 (by decide) (by decide) with h63 | h63
              · rcases m.htr 0 4 5 (by decide) (by decide) with h64 | h64
                · rcases m.htr 1 2 3 (by decide) (by decide) with h65 | h65
                  · linarith only [h3, h61, h65, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h67 | h67
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h69 | h69
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                              · linarith only [h3, h61, h70, h72, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                              · linarith only [h72, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h3, h71, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h3, h61, h68, h70, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h68, h69, hc34, hlam, hphi, ht45, u5elo4]
                      · linarith only [h3, h61, h63, h65, h67, h68, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h67, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h64, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h3, h61, h63, hlam]
            · linarith only [h61, h62, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h83 | h83
            · rcases m.htr 0 3 4 (by decide) (by decide) with h84 | h84
              · rcases m.htr 0 4 5 (by decide) (by decide) with h85 | h85
                · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
                  · linarith only [h3, h86, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
                              · linarith only [h1, h89, h93, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h93, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h61, h91, h92, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h3, h84, h88, h91, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h90, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h3, h84, h86, h88, h89, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h88, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h85, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
                · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                  · linarith only [h0, h103, h3, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                      · linarith only [h1, h106, h84, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                          · linarith only [h0, h105, h109, h3, h84, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                              · rcases h0bigk with h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h105, h111, h112, hc45, hlam, hphi, ht0b, ht5b, p113_1, u0elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h105, h111, h112, h3, hc45, hlam, hphi, ht0b, ht5b, p113_1, u0elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h105, h111, h112, h61, hc45, hlam, hphi, ht0b, ht5b, p113_1, u0elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 1) (by simp) with h118 | h118
                                  · rcases p113_3 (m.d 0 2) (by simp) with h119 | h119
                                    · linarith only [h0, h119, hlam]
                                    · linarith only [h119, h83, hlam]
                                  · linarith only [h118, h2, hlam]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, hlam, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h3, hlam, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h61, hlam, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h109, h3, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h1, hlam, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h105, h84, hc25, hlam, hphi, ht0b, ht5b, p113_1, u0elo3]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h84, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 1) (by simp) with h132 | h132
                                  · rcases p113_3 (m.d 0 2) (by simp) with h133 | h133
                                    · linarith only [h133, h3, hlam]
                                    · linarith only [h133, h83, hlam]
                                  · linarith only [h132, h2, hlam]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h61, hc01, hlam, hphi, ht12, p113_1, u2elo3]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h61, hc02, hlam, hphi, p113_1, u2elo3]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h1, h103, h61, hc12, hlam, hphi, p113_1, u2elo3]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 1) (by simp) with h141 | h141
                                  · rcases p113_3 (m.d 0 2) (by simp) with h142 | h142
                                    · linarith only [h142, h61, hlam]
                                    · linarith only [h142, h83, hlam]
                                  · linarith only [h141, h2, hlam]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h2, hlam, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h83, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, h105, h111, h112, h3, hc45, hlam, hphi, ht0b, ht5b, p113_1, u0elo4]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h102, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                              · linarith only [h0, h105, h109, h111, h112, h3, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h111, h3, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h108, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h105, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h102, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h83, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h158 | h158
      · rcases m.htr 0 2 3 (by decide) (by decide) with h159 | h159
        · linarith only [h0, h1, h159, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h161 | h161
          · rcases m.htr 0 2 5 (by decide) (by decide) with h162 | h162
            · rcases m.htr 0 3 4 (by decide) (by decide) with h163 | h163
              · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
                  · linarith only [h0, h159, h165, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h165, hc12, hlam, hphi, u2elo2]
                · linarith only [h164, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h0, h1, h161, h163, hlam]
            · linarith only [h162, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h171 | h171
            · rcases m.htr 0 3 4 (by decide) (by decide) with h172 | h172
              · rcases m.htr 0 4 5 (by decide) (by decide) with h173 | h173
                · rcases m.htr 1 2 3 (by decide) (by decide) with h174 | h174
                  · linarith only [h0, h1, h159, h174, hlam]
                  · linarith only [h0, h1, h174, hc12, hlam, hphi, u2elo2]
                · linarith only [h161, h171, h173, hc25, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                  · linarith only [h0, h1, h172, h179, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h179, hc12, hlam, hphi, u2elo2]
                · linarith only [h172, h178, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h171, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h158, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h185 | h185
    · rcases m.htr 0 1 5 (by decide) (by decide) with h186 | h186
      · rcases m.htr 0 2 3 (by decide) (by decide) with h187 | h187
        · rcases m.htr 0 2 4 (by decide) (by decide) with h188 | h188
          · rcases m.htr 0 2 5 (by decide) (by decide) with h189 | h189
            · rcases m.htr 0 3 4 (by decide) (by decide) with h190 | h190
              · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
                · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h193 | h193
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h194 | h194
                      · linarith only [h0, h185, h194, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h185, h190, h192, h194, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h193, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h192, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h191, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h200 | h200
                · rcases m.htr 1 2 3 (by decide) (by decide) with h201 | h201
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h202 | h202
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h203 | h203
                      · linarith only [h185, h190, h203, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                          · linarith only [h185, h190, h201, h206, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                            · linarith only [h0, h185, h201, h208, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h208, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h205, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h202, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h185, h201, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h200, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h189, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h216 | h216
            · rcases m.htr 0 3 4 (by decide) (by decide) with h217 | h217
              · linarith only [h0, h185, h188, h217, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h219 | h219
                · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h222 | h222
                      · linarith only [h0, h185, h188, h217, h222, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h224 | h224
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                          · linarith only [h0, h185, h188, h217, h220, h225, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                            · linarith only [h0, h185, h188, h220, h227, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                            · linarith only [h227, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h224, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h221, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h220, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h188, h219, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h0, h185, h216, hc13, hlam, hphi, ht34, ht45, u5elo2]
        · linarith only [h0, h185, h187, hlam]
      · linarith only [h185, h186, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h237 | h237
      · rcases m.htr 0 2 3 (by decide) (by decide) with h238 | h238
        · rcases m.htr 0 2 4 (by decide) (by decide) with h239 | h239
          · rcases m.htr 0 2 5 (by decide) (by decide) with h240 | h240
            · rcases m.htr 0 3 4 (by decide) (by decide) with h241 | h241
              · rcases m.htr 0 4 5 (by decide) (by decide) with h242 | h242
                · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h245 | h245
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h249 | h249
                              · linarith only [h0, h238, h247, h249, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h249, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h248, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h253 | h253
                            · linarith only [h0, h238, h241, h247, h253, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h253, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h245, h246, hc34, hlam, hphi, ht45, u5elo4]
                      · linarith only [h0, h185, h238, h241, h245, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h244, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h237, h238, h243, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h242, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h261 | h261
                · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                      · linarith only [h185, h237, h241, h262, h263, h264, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                          · linarith only [h185, h237, h263, h264, h267, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h269 | h269
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h270 | h270
                              · rcases h0bigk with h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h0, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h185, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h185, h241, hlam, p271_1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h185, h264, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p271_1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p271_1, u2elo1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h0, h185, h237, h263, h269, h270, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p271_1, u2elo1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h0, h185, h237, h241, h263, h269, h270, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p271_1, u2elo1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  rcases p271_3 (m.d 0 1) (by simp) with h281 | h281
                                  · linarith only [h0, h281, hlam]
                                  · linarith only [h237, h281, hlam]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h237, h263, h269, h270, hc45, hlam, hphi, ht0b, ht5b, p271_1, u0elo2]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h238, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h241, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  rcases p271_3 (m.d 0 1) (by simp) with h288 | h288
                                  · linarith only [h185, h288, hlam]
                                  · linarith only [h237, h288, hlam]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h0, h237, h239, h263, h269, h270, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p271_1, u2elo1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h239, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h0, h185, h237, h239, h263, h269, h270, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p271_1, u2elo1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  rcases p271_3 (m.d 0 1) (by simp) with h295 | h295
                                  · linarith only [h185, h241, h295, hlam]
                                  · linarith only [h237, h295, hlam]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h237, hlam, p271_1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h240, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h185, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p271_1, u5elo0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h261, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hlam, p271_0]
                              · linarith only [h185, h237, h263, h264, h269, h270, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h269, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h185, h237, h263, h264, h266, hc25, hlam, hphi, u5elo4]
                    · linarith only [h185, h262, h263, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h237, h262, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h185, h237, h241, h261, hc15, hlam, hphi, u5elo4]
            · linarith only [h240, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h310 | h310
            · rcases m.htr 0 3 4 (by decide) (by decide) with h311 | h311
              · linarith only [h238, h239, h311, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h313 | h313
                · rcases m.htr 1 2 3 (by decide) (by decide) with h314 | h314
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h315 | h315
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h316 | h316
                      · linarith only [h185, h237, h311, h314, h315, h316, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h318 | h318
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
                          · linarith only [h238, h316, h319, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h321 | h321
                            · linarith only [h238, h239, h321, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                            · linarith only [h321, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h185, h237, h315, h316, h318, hc25, hlam, hphi, u5elo4]
                    · linarith only [h315, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h237, h314, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h313, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h185, h237, h238, h310, hc15, hlam, hphi, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h329 | h329
          · rcases m.htr 0 2 5 (by decide) (by decide) with h330 | h330
            · rcases m.htr 0 3 4 (by decide) (by decide) with h331 | h331
              · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
                · rcases m.htr 1 2 3 (by decide) (by decide) with h333 | h333
                  · linarith only [h238, h333, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h237, h333, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h332, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h238, h329, h331, hlam]
            · linarith only [h329, h330, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h339 | h339
            · rcases m.htr 0 3 4 (by decide) (by decide) with h340 | h340
              · rcases m.htr 0 4 5 (by decide) (by decide) with h341 | h341
                · rcases m.htr 1 2 3 (by decide) (by decide) with h342 | h342
                  · linarith only [h238, h342, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h237, h342, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h0, h237, h329, h341, hc15, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h346 | h346
                · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                  · linarith only [h0, h237, h238, h347, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h237, h347, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h340, h346, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h0, h237, h339, hc15, hlam, hphi, u5elo2]
      · linarith only [h237, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT2_M_LI_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h2ehi := hb2.1
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo2]

theorem n7l_sBT2_M_LI_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · linarith only [h0, h1, h3, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h6 | h6
    · linarith only [h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi2]
      · linarith only [h0, h8, hc01, hlam, hphi, ht12, u2elo4]

theorem n7l_sBT2_M_LI_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have h2ehi := hb2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
    · linarith only [h0, h1, hc25, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
        · linarith only [h0, h6, h8, hc24, hlam, hphi, u2ehi0]
        · linarith only [h0, h8, hc45, hlam, hphi, ht23, ht34, u2ehi0]

theorem n7l_sBT2_M_LI_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LI_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h2ehi := hb2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht23, ht34, ht45, p0_1, u2ehi4, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht23, ht34, ht45, p0_1, u2ehi4, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LI_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                    · linarith only [h7, h9, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h12, h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
                    · linarith only [h12, h7, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h4, h7, hc12, hlam, hphi, u2elo0]
              · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h17 | h17
              · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h0, h20, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                    · linarith only [h19, h20, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h19, h23, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
                    · linarith only [h18, h23, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h18, h4, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                    · linarith only [h0, h29, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                    · linarith only [h28, h29, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h28, h32, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
                    · linarith only [h27, h32, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h27, h4, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h36 | h36
            · rcases m.htr 0 3 5 (by decide) (by decide) with h37 | h37
              · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                · linarith only [h38, h4, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
                    · linarith only [h0, h4, h41, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
                    · linarith only [h40, h41, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                    · linarith only [h40, h44, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
                        · linarith only [h1, h47, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                        · linarith only [h37, h46, h47, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h36, h38, h4, h46, hc12, hlam, hphi, u2elo2]
              · linarith only [h36, h37, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h52 | h52
              · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                · linarith only [h4, h53, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                    · linarith only [h0, h4, h56, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
                    · linarith only [h55, h56, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h55, h59, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                      · linarith only [h1, h36, h52, h61, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                        · linarith only [h2, h61, h63, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                        · linarith only [h36, h52, h63, hc13, hc34, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
                · linarith only [h0, h4, h52, h66, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h68 | h68
                  · linarith only [h0, h4, h52, h68, hc24, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                    · linarith only [h0, h4, h52, h70, hlam, hphi, u5ehi7, u5elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                      · linarith only [h1, h52, h72, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                        · linarith only [h1, h52, h74, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                          · linarith only [h2, h76, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                            · linarith only [h36, h4, h78, hc02, hlam, hphi, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                              · linarith only [h0, h4, h52, h78, h80, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h4, h80, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h84 | h84
        · rcases m.htr 0 2 3 (by decide) (by decide) with h85 | h85
          · rcases m.htr 0 3 4 (by decide) (by decide) with h86 | h86
            · linarith only [h1, h2, h86, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
                · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
                  · linarith only [h0, h2, h85, h88, h90, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                  · linarith only [h0, h2, h85, h88, h90, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi8]
                · linarith only [h85, h89, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                  · linarith only [h0, h2, h95, hlam]
                  · linarith only [h0, h2, h94, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h85, h94, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h99 | h99
            · linarith only [h1, h2, h99, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h101 | h101
              · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                · linarith only [h102, h85, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                  · linarith only [h1, h102, h104, h2, hlam]
                  · linarith only [h1, h102, h104, h2, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
                · linarith only [h0, h101, h107, h85, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                  · linarith only [h0, h101, h109, h85, hc24, hlam, hphi, ht45, u5elo3]
                  · linarith only [h109, h2, h84, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi6]
        · linarith only [h0, h84, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h113 | h113
      · rcases m.htr 0 1 5 (by decide) (by decide) with h114 | h114
        · rcases m.htr 0 2 3 (by decide) (by decide) with h115 | h115
          · linarith only [h0, h1, h115, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h117 | h117
            · rcases m.htr 0 3 5 (by decide) (by decide) with h118 | h118
              · rcases m.htr 1 2 3 (by decide) (by decide) with h119 | h119
                · linarith only [h115, h119, hc02, hlam, hphi, u2elo1]
                · linarith only [h1, h114, h119, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi6]
              · linarith only [h1, h114, h118, hlam, hphi, u5ehi6, u5elo3]
            · linarith only [h1, h113, h117, hlam]
        · linarith only [h113, h114, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h125 | h125
        · rcases m.htr 0 2 3 (by decide) (by decide) with h126 | h126
          · linarith only [h0, h1, h126, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h128 | h128
            · rcases m.htr 0 3 5 (by decide) (by decide) with h129 | h129
              · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
                · linarith only [h126, h130, hc02, hlam, hphi, u2elo1]
                · linarith only [h1, h125, h130, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi6]
              · linarith only [h113, h125, h128, h129, hlam, hphi, u5ehi6, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h134 | h134
              · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                · linarith only [h0, h1, h128, h135, hc23, hc34, hlam, hphi]
                · linarith only [h0, h1, h135, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h125, h134, hlam, hphi, u5ehi6, u5elo3]
        · linarith only [h0, h125, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h140 | h140
    · rcases m.htr 0 1 4 (by decide) (by decide) with h141 | h141
      · rcases m.htr 0 1 5 (by decide) (by decide) with h142 | h142
        · linarith only [h0, h142, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
        · linarith only [h141, h142, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h145 | h145
        · linarith only [h0, h145, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
        · linarith only [h140, h145, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h148 | h148
      · rcases m.htr 0 1 5 (by decide) (by decide) with h149 | h149
        · linarith only [h0, h149, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
        · linarith only [h148, h149, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h152 | h152
        · linarith only [h0, h152, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h154 | h154
          · rcases m.htr 0 3 4 (by decide) (by decide) with h155 | h155
            · rcases m.htr 0 3 5 (by decide) (by decide) with h156 | h156
              · rcases m.htr 1 2 3 (by decide) (by decide) with h157 | h157
                · rcases m.htr 1 2 4 (by decide) (by decide) with h158 | h158
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h161 | h161
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h162 | h162
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h163 | h163
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                              · linarith only [h154, h164, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                              · linarith only [h0, h154, h156, h163, h164, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h167 | h167
                              · linarith only [h155, h163, h167, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi8]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h169 | h169
                                · linarith only [h158, h169, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h171 | h171
                                  · linarith only [h0, h154, h155, h163, h169, h171, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                  · linarith only [h157, h160, h162, h163, h171, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h148, h162, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h140, h154, h156, h161, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h140, h155, h160, hlam]
                    · linarith only [h0, h154, h156, h159, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi8]
                  · linarith only [h0, h154, h156, h158, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi8]
                · linarith only [h0, h154, h156, h157, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
              · linarith only [h155, h156, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h181 | h181
              · rcases m.htr 1 2 3 (by decide) (by decide) with h182 | h182
                · rcases m.htr 1 2 4 (by decide) (by decide) with h183 | h183
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h184 | h184
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                      · linarith only [h155, h181, h185, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h188 | h188
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h189 | h189
                            · linarith only [h140, h185, h189, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h191 | h191
                              · linarith only [h154, h191, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                              · linarith only [h140, h181, h185, h191, hc23, hc34, hlam, hphi]
                          · linarith only [h148, h155, h181, h188, hlam, hphi, u5ehi8, u5elo4]
                        · linarith only [h140, h181, h187, hlam]
                    · linarith only [h183, h184, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h140, h181, h182, h183, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi8]
                · linarith only [h0, h182, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
                · rcases m.htr 1 2 4 (by decide) (by decide) with h200 | h200
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
                      · linarith only [h140, h155, h199, h202, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
                        · linarith only [h140, h181, h202, h204, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h140, h204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h200, h201, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h140, h199, h200, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h154, h199, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h210 | h210
            · rcases m.htr 0 3 5 (by decide) (by decide) with h211 | h211
              · rcases m.htr 1 2 3 (by decide) (by decide) with h212 | h212
                · linarith only [h154, h212, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h212, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h210, h211, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h216 | h216
              · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                · linarith only [h0, h154, h217, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h217, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
                · linarith only [h0, h154, h220, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h220, hc01, hlam, hphi, ht12, u2elo2]

theorem n7l_sBT2_M_LI_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2bigk := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h0, h2, h4, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
            · linarith only [h0, h1, h10, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
              · linarith only [h0, h1, h12, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h1, h15, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                  · linarith only [h10, h14, h15, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h1, h18, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                  · linarith only [h18, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h2, h3, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
        · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
          · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
            · linarith only [h0, h2, h22, h24, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
              · linarith only [h0, h26, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · linarith only [h2, h22, h26, hc12, hc24, hlam, hphi]
          · linarith only [h1, h2, h23, hc12, hc24, hlam, hphi]
        · linarith only [h1, h22, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h31 | h31
      · rcases m.htr 0 2 5 (by decide) (by decide) with h32 | h32
        · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
          · linarith only [h1, h32, h33, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
            · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
              · linarith only [h0, h36, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · linarith only [h1, h32, h36, hc12, hc23, hlam, hphi]
            · linarith only [h1, h31, h35, hc12, hc23, hlam, hphi]
        · linarith only [h31, h32, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h41 | h41
        · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
          · linarith only [h1, h41, h42, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
            · linarith only [h0, h31, h41, h44, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
              · linarith only [h0, h46, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · linarith only [h1, h41, h46, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
          · linarith only [h0, h1, h41, h49, hc03, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
            · linarith only [h0, h31, h51, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
              · linarith only [h0, h41, h53, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                    · rcases h2bigk with h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h41, hc12, hlam, hphi, ht23, ht34, ht45, p58_1, u5elo2]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h1, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h31, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h41, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h0, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h49, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h51, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h53, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        rcases p58_3 (m.d 0 2) (by simp) with h69 | h69
                        · linarith only [h69, hlam, p58_0]
                        · rcases p58_3 (m.d 1 2) (by simp) with h71 | h71
                          · linarith only [h49, h71, hlam]
                          · rcases p58_3 (m.d 2 3) (by simp) with h73 | h73
                            · rcases p58_3 (m.d 2 4) (by simp) with h74 | h74
                              · linarith only [h55, h74, hlam]
                              · linarith only [h31, h74, hlam]
                            · linarith only [h73, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        rcases p58_3 (m.d 0 2) (by simp) with h78 | h78
                        · linarith only [h1, h78, hlam]
                        · linarith only [h0, h78, hlam]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h57, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p58_1, u5ehi9]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h0, h41, hc12, hc23, hlam, hphi, p58_1]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        rcases p58_3 (m.d 0 2) (by simp) with h84 | h84
                        · linarith only [h84, hlam, p58_0]
                        · rcases p58_3 (m.d 1 2) (by simp) with h86 | h86
                          · linarith only [h51, h86, hlam]
                          · rcases p58_3 (m.d 2 3) (by simp) with h88 | h88
                            · rcases p58_3 (m.d 2 4) (by simp) with h89 | h89
                              · rcases p58_3 (m.d 2 5) (by simp) with h90 | h90
                                · linarith only [h57, h90, hlam]
                                · linarith only [h41, h90, hlam]
                              · linarith only [h89, hlam, p58_0]
                            · linarith only [h1, h88, hlam]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        rcases p58_3 (m.d 0 2) (by simp) with h95 | h95
                        · linarith only [h31, h95, hlam]
                        · linarith only [h0, h95, hlam]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h55, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h0, h41, hc12, hc24, hlam, hphi, p58_1]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p58_1, u5elo2]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p58_1, u5elo2]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h56, hlam, p58_1]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h57, hlam, p58_1]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hlam, p58_0]
                    · linarith only [h0, h31, h57, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h1, h56, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h109 | h109
                    · rcases h2bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h1, hc12, hc23, hlam, hphi, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h1, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h31, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h41, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h0, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h49, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h51, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h53, hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h55, hc02, hc34, hlam, hphi, ht23, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h55, hc12, hc34, hlam, hphi, ht23, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h55, hlam, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h41, h55, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p110_1, u5ehi5]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        rcases p110_3 (m.d 0 2) (by simp) with h126 | h126
                        · linarith only [h126, hlam, p110_0]
                        · rcases p110_3 (m.d 1 2) (by simp) with h128 | h128
                          · linarith only [h128, h51, hlam]
                          · rcases p110_3 (m.d 2 3) (by simp) with h130 | h130
                            · linarith only [h130, h55, hlam]
                            · linarith only [h1, h130, hlam]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        rcases p110_3 (m.d 0 2) (by simp) with h133 | h133
                        · linarith only [h133, h31, hlam]
                        · linarith only [h0, h133, hlam]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h0, h1, h55, hc12, hc34, hlam, hphi, ht23, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [hlam, p110_0]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h0, h41, h55, hc12, hc34, hlam, hphi, ht23, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p110_1, u5elo2]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p110_1, u5elo2]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h108, hlam, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [h109, hlam, p110_1]
                      · have p110_0 := h110c.1
                        have p110_1 := h110c.2.1
                        have p110_2 := h110c.2.2.1
                        have p110_3 := h110c.2.2.2
                        linarith only [hlam, p110_0]
                    · linarith only [h0, h109, h31, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h1, h108, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h146 | h146
    · rcases m.htr 0 2 4 (by decide) (by decide) with h147 | h147
      · rcases m.htr 0 2 5 (by decide) (by decide) with h148 | h148
        · rcases m.htr 1 2 3 (by decide) (by decide) with h149 | h149
          · rcases m.htr 1 2 4 (by decide) (by decide) with h150 | h150
            · rcases m.htr 1 2 5 (by decide) (by decide) with h151 | h151
              · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                · rcases m.htr 2 3 5 (by decide) (by decide) with h153 | h153
                  · linarith only [h146, h153, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                  · linarith only [h152, h153, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                  · linarith only [h146, h156, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h158 | h158
                    · linarith only [h147, h158, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
                    · rcases h2bigk with h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h0, hlam, p160_1]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        rcases p160_3 (m.d 0 2) (by simp) with h163 | h163
                        · rcases p160_3 (m.d 1 2) (by simp) with h164 | h164
                          · rcases p160_3 (m.d 2 3) (by simp) with h165 | h165
                            · linarith only [h165, hlam, p160_0]
                            · rcases p160_3 (m.d 2 4) (by simp) with h167 | h167
                              · linarith only [h147, h167, hlam]
                              · linarith only [h152, h167, hlam]
                          · linarith only [h149, h164, hlam]
                        · linarith only [h163, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        rcases p160_3 (m.d 0 2) (by simp) with h172 | h172
                        · rcases p160_3 (m.d 1 2) (by simp) with h173 | h173
                          · rcases p160_3 (m.d 2 3) (by simp) with h174 | h174
                            · linarith only [h146, h174, hlam]
                            · rcases p160_3 (m.d 2 4) (by simp) with h176 | h176
                              · linarith only [h176, hlam, p160_0]
                              · rcases p160_3 (m.d 2 5) (by simp) with h178 | h178
                                · linarith only [h148, h178, hlam]
                                · linarith only [h158, h178, hlam]
                          · linarith only [h150, h173, hlam]
                        · linarith only [h172, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, hphi, ht0b, ht5b, p160_1, u0elo1, u5ehi7]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h148, hc12, hlam, hphi, ht01, ht0b, ht5b, p160_1, u5ehi7]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        rcases p160_3 (m.d 0 2) (by simp) with h186 | h186
                        · linarith only [h0, h186, hlam]
                        · linarith only [h146, h186, hlam]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        rcases p160_3 (m.d 0 2) (by simp) with h189 | h189
                        · linarith only [h0, h189, hlam]
                        · linarith only [h147, h189, hlam]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        rcases p160_3 (m.d 0 2) (by simp) with h192 | h192
                        · linarith only [h0, h192, hlam]
                        · linarith only [h148, h192, hlam]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h146, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h149, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h152, hlam, p160_1]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h156, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h147, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h150, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h147, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p160_1, u0elo1]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h158, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h148, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h151, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h148, hc23, hlam, hphi, ht34, ht45, p160_1, u5elo0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h148, hc24, hlam, hphi, ht45, p160_1, u5elo0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, p160_0]
              · linarith only [h0, h148, h151, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
            · linarith only [h0, h147, h150, hlam]
          · linarith only [h0, h146, h149, hlam]
        · linarith only [h146, h148, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h214 | h214
        · rcases m.htr 1 2 3 (by decide) (by decide) with h215 | h215
          · rcases m.htr 1 2 4 (by decide) (by decide) with h216 | h216
            · linarith only [h147, h214, h216, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h218 | h218
              · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                · linarith only [h0, h146, h216, h219, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h221 | h221
                  · linarith only [h0, h146, h216, h219, h221, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h223 | h223
                    · rcases h2bigk with h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h0, hlam, p224_1]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h0, h216, h219, hc23, hc34, hlam, hphi, p224_1]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h147, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h0, h216, h219, h223, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p224_1, u5ehi9]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h216, h219, hc02, hc34, hlam, hphi, ht23, p224_1]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h216, h219, hc23, hc34, hlam, hphi, p224_1]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h216, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h216, h219, h223, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p224_1, u5ehi9]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h146, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h215, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h219, hlam, p224_1]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h221, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h214, h219, h223, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p224_1, u5ehi9]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h0, h219, hc01, hc34, hlam, hphi, ht12, ht23, p224_1]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        rcases p224_3 (m.d 0 2) (by simp) with h242 | h242
                        · linarith only [h147, h242, hlam]
                        · linarith only [h146, h242, hlam]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        rcases p224_3 (m.d 0 2) (by simp) with h246 | h246
                        · linarith only [h147, h246, hlam]
                        · linarith only [h214, h246, hlam]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h214, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h218, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h214, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1, u0elo1]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h223, hlam, p224_1]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hlam, p224_0]
                    · linarith only [h0, h214, h216, h223, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
              · linarith only [h0, h214, h218, hlam]
          · linarith only [h0, h146, h214, h215, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi7]
        · linarith only [h146, h214, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h258 | h258
      · rcases m.htr 0 2 5 (by decide) (by decide) with h259 | h259
        · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
          · linarith only [h146, h259, h260, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
            · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
              · rcases m.htr 2 3 4 (by decide) (by decide) with h264 | h264
                · rcases m.htr 2 3 5 (by decide) (by decide) with h265 | h265
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h266 | h266
                    · linarith only [h258, h266, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
                    · rcases h2bigk with h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h0, hlam, p268_1]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h146, hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        rcases p268_3 (m.d 0 2) (by simp) with h272 | h272
                        · rcases p268_3 (m.d 1 2) (by simp) with h273 | h273
                          · rcases p268_3 (m.d 2 3) (by simp) with h274 | h274
                            · rcases p268_3 (m.d 2 4) (by simp) with h275 | h275
                              · linarith only [h275, hlam, p268_0]
                              · rcases p268_3 (m.d 2 5) (by simp) with h277 | h277
                                · linarith only [h259, h277, hlam]
                                · linarith only [h266, h277, hlam]
                            · linarith only [h264, h274, hlam]
                          · linarith only [h262, h273, hlam]
                        · linarith only [h272, hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h0, h260, h265, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p268_1, u5ehi8]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h260, hc02, hc23, hlam, hphi, p268_1]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h260, hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        rcases p268_3 (m.d 0 2) (by simp) with h287 | h287
                        · linarith only [h0, h287, hlam]
                        · linarith only [h258, h287, hlam]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h260, h265, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p268_1, u5ehi8]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h259, h265, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p268_1, u5ehi8]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p268_1]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        rcases p268_3 (m.d 0 2) (by simp) with h294 | h294
                        · linarith only [h146, h294, hlam]
                        · linarith only [h258, h294, hlam]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        rcases p268_3 (m.d 0 2) (by simp) with h297 | h297
                        · linarith only [h146, h297, hlam]
                        · linarith only [h259, h297, hlam]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h258, hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h262, hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h264, hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h266, hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h259, hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h263, hlam, p268_0]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h265, hlam, p268_1]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [h259, hc24, hlam, hphi, ht0b, ht45, ht5b, p268_1, u0elo1]
                      · have p268_0 := h268c.1
                        have p268_1 := h268c.2.1
                        have p268_2 := h268c.2.2.1
                        have p268_3 := h268c.2.2.2
                        linarith only [hlam, p268_0]
                  · linarith only [h0, h259, h260, h265, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h0, h259, h260, h264, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · linarith only [h0, h259, h263, hlam]
            · linarith only [h0, h258, h262, hlam]
        · linarith only [h258, h259, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h315 | h315
        · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
          · linarith only [h146, h315, h316, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
            · linarith only [h258, h315, h316, h318, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
              · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
                · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h323 | h323
                    · rcases h2bigk with h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h0, hlam, p324_1]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h146, hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h258, hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h322, hlam, hphi, ht0b, ht5b, p324_1, u0elo1, u5ehi8]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h318, h321, hc02, hc23, hlam, hphi, p324_1]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h316, hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h318, hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h318, h321, h322, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p324_1, u5ehi8]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h315, h322, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p324_1, u5ehi8]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p324_1]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h258, h315, h322, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p324_1, u5ehi8]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        rcases p324_3 (m.d 0 2) (by simp) with h339 | h339
                        · linarith only [h146, h339, hlam]
                        · linarith only [h315, h339, hlam]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h315, h322, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p324_1, u5ehi8]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h0, h315, h322, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p324_1, u5ehi8]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h321, hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        rcases p324_3 (m.d 0 2) (by simp) with h346 | h346
                        · linarith only [h258, h346, hlam]
                        · linarith only [h315, h346, hlam]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h315, hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h320, hlam, p324_0]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h322, hlam, p324_1]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [h323, hlam, p324_1]
                      · have p324_0 := h324c.1
                        have p324_1 := h324c.2.1
                        have p324_2 := h324c.2.2.1
                        have p324_3 := h324c.2.2.2
                        linarith only [hlam, p324_0]
                    · linarith only [h258, h315, h322, h323, hlam, hphi, u5ehi8, u5elo4]
                  · linarith only [h321, h322, hc34, hlam, hphi, ht45, u5elo3]
                · linarith only [h0, h315, h316, h321, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · linarith only [h0, h315, h320, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
          · rcases m.htr 1 2 4 (by decide) (by decide) with h359 | h359
            · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
              · rcases m.htr 2 3 4 (by decide) (by decide) with h361 | h361
                · rcases m.htr 2 3 5 (by decide) (by decide) with h362 | h362
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h363 | h363
                    · rcases h2bigk with h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h0, hlam, p364_1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h146, hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h258, hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h315, hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        rcases p364_3 (m.d 0 2) (by simp) with h370 | h370
                        · linarith only [h0, h370, hlam]
                        · rcases p364_3 (m.d 1 2) (by simp) with h372 | h372
                          · rcases p364_3 (m.d 2 3) (by simp) with h373 | h373
                            · linarith only [h358, h373, hlam]
                            · linarith only [h146, h373, hlam]
                          · linarith only [h0, h372, hlam]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h361, h363, hc12, hlam, hphi, ht01, ht0b, ht5b, p364_1, u5ehi9]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h0, h315, h360, h363, hc01, hc12, hlam, hphi, p364_1, u5ehi9, u5elo1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h0, h315, hc01, hc12, hlam, hphi, p364_1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h0, h358, hc01, hc12, hlam, hphi, p364_1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h358, hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h0, h315, h358, h360, h363, hc01, hc12, hlam, hphi, p364_1, u5ehi9, u5elo1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h0, h315, h358, hc01, hc12, hlam, hphi, p364_1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h0, h359, hc01, hc12, hlam, hphi, p364_1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h359, hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h361, hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h0, h315, h358, h361, hc01, hc12, hlam, hphi, p364_1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h0, h360, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p364_1, u5elo1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h360, hlam, p364_0]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h362, hlam, p364_1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [h363, hlam, p364_1]
                      · have p364_0 := h364c.1
                        have p364_1 := h364c.2.1
                        have p364_2 := h364c.2.2.1
                        have p364_3 := h364c.2.2.2
                        linarith only [hlam, p364_0]
                    · linarith only [h0, h258, h363, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h361, h362, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h398 | h398
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h399 | h399
                    · rcases h2bigk with h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [hlam, p400_0]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h0, hlam, p400_1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h146, hlam, p400_0]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h258, hlam, p400_0]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h315, hlam, p400_0]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        rcases p400_3 (m.d 0 2) (by simp) with h406 | h406
                        · linarith only [h0, h406, hlam]
                        · rcases p400_3 (m.d 1 2) (by simp) with h408 | h408
                          · rcases p400_3 (m.d 2 3) (by simp) with h409 | h409
                            · linarith only [h358, h409, hlam]
                            · linarith only [h146, h409, hlam]
                          · linarith only [h0, h408, hlam]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [hlam, p400_0]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h0, h315, h360, h398, hc01, hc12, hlam, hphi, p400_1, u5ehi8, u5elo1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h0, h315, h360, h361, h398, hc01, hc12, hlam, hphi, p400_1, u5ehi8, u5elo1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h0, h315, hc01, hc12, hlam, hphi, p400_1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h0, h361, hc01, hc34, hlam, hphi, ht12, ht23, p400_1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h358, hlam, p400_0]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [hlam, p400_0]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h361, hlam, p400_1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h0, h315, h361, hc01, hc34, hlam, hphi, ht12, ht23, p400_1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h0, h359, hc01, hc12, hlam, hphi, p400_1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h359, hlam, p400_0]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h0, h146, h359, hc01, hc12, hlam, hphi, p400_1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [hlam, p400_0]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h0, h315, h359, hc01, hc12, hlam, hphi, p400_1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h0, h360, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p400_1, u5elo1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h360, hlam, p400_0]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h398, hlam, p400_1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [h399, hlam, p400_1]
                      · have p400_0 := h400c.1
                        have p400_1 := h400c.2.1
                        have p400_2 := h400c.2.2.1
                        have p400_3 := h400c.2.2.2
                        linarith only [hlam, p400_0]
                    · linarith only [h0, h258, h399, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h146, h398, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h360, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h146, h358, h359, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h436 | h436
            · linarith only [h0, h258, h358, h436, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h438 | h438
              · linarith only [h0, h315, h358, h438, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h438, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem n7l_sBT2_M_LI_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2ehi := hb2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · linarith only [h0, h6, hc23, hlam, hphi, u2ehi4]
    · linarith only [h6, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem n7l_sBT2_M_LR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5bigk := hb5.1
  have h2elo := hb2.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
    · linarith only [h8, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h8, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
    · linarith only [h11, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h11, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
    · linarith only [h14, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h14, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi9, u2elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h23 | h23
    · linarith only [h23, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h23, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h26 | h26
    · linarith only [h26, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h26, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h30 | h30
    · linarith only [h30, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h30, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h34 | h34
    · linarith only [h34, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h34, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h37 | h37
    · linarith only [h37, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h37, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
    · linarith only [h40, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h40, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5bigk := hb5.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
    · linarith only [h8, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h8, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
    · linarith only [h11, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h11, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
    · linarith only [h14, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h14, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h18 | h18
    · linarith only [h18, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h18, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
    · linarith only [h22, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h22, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h25 | h25
    · linarith only [h25, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h25, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
    · linarith only [h29, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h29, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h32 | h32
    · linarith only [h32, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h32, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h36 | h36
    · linarith only [h36, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h36, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
    · linarith only [h40, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h40, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h43 | h43
    · linarith only [h43, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h43, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h46 | h46
    · linarith only [h46, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h46, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5bigk := hb5.1
  have h2ehi := hb2.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h9 | h9
    · linarith only [h9, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h9, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h12 | h12
    · linarith only [h12, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h12, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h16 | h16
    · linarith only [h16, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h16, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h20 | h20
    · linarith only [h20, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h20, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h23 | h23
    · linarith only [h23, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h23, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h27 | h27
    · linarith only [h27, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h27, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht23, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h32 | h32
    · linarith only [h32, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h32, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h36, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
    · linarith only [h40, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h40, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo0]

theorem n7l_sBT2_M_LR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo0]

theorem n7l_sBT2_M_LR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo0]

theorem n7l_sBT2_M_LR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.1
  have h2elo := hb2.1
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi6, u2elo4]

theorem n7l_sBT2_M_LR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
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
  have h5ehi := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h2, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
            · linarith only [h0, h2, h4, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h2, h5, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h0, h11, h12, h14, h2, h7, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                      · linarith only [h0, h11, h12, h14, h2, hc34, hc45, hlam, hphi]
                  · linarith only [h11, h4, h5, hc23, hc35, hlam, hphi]
                · linarith only [h1, h10, h2, hc12, hc25, hlam, hphi]
              · linarith only [h0, h2, h9, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h20 | h20
          · linarith only [h20, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
            · linarith only [h1, h2, h22, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
              · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                  · linarith only [h0, h2, h26, h4, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                    · linarith only [h1, h2, h20, h26, h28, hc25, hlam, hphi, ht01, ht12, u0ehi7]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                      · linarith only [h22, h30, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                      · linarith only [h30, h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                · linarith only [h1, h2, h25, hc12, hc25, hlam, hphi]
              · linarith only [h0, h2, h24, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h35 | h35
      · linarith only [h35, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h37 | h37
        · linarith only [h0, h1, h37, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h39 | h39
          · linarith only [h0, h1, h39, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
            · linarith only [h41, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
              · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                · linarith only [h1, h44, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                  · linarith only [h37, h46, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                    · linarith only [h0, h39, h48, hlam, hphi, u0ehi7, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                      · linarith only [h0, h1, h41, h50, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1, h46, h50, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h0, h1, h43, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h54 | h54
    · rcases m.htr 0 2 5 (by decide) (by decide) with h55 | h55
      · linarith only [h0, h55, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h57 | h57
        · rcases m.htr 0 3 5 (by decide) (by decide) with h58 | h58
          · linarith only [h58, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h60 | h60
            · linarith only [h0, h54, h58, h60, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
              · linarith only [h0, h62, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h66 | h66
                    · linarith only [h58, h66, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                    · linarith only [h0, h54, h66, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                  · linarith only [h0, h54, h65, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                · linarith only [h0, h54, h64, hc12, hc23, hlam, hphi]
        · linarith only [h0, h54, h57, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h72 | h72
      · linarith only [h72, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
        · rcases m.htr 0 3 5 (by decide) (by decide) with h75 | h75
          · linarith only [h75, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
            · linarith only [h74, h75, h77, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
              · linarith only [h0, h79, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                · linarith only [h54, h81, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                    · linarith only [h75, h84, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                    · linarith only [h0, h84, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h0, h74, h83, hlam, hphi, u0ehi6, u0elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h88 | h88
          · linarith only [h88, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h90 | h90
            · linarith only [h90, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
              · linarith only [h0, h92, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                · linarith only [h54, h94, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                  · linarith only [h74, h96, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · linarith only [h0, h96, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]

theorem n7l_sBT2_M_LR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.1
  have h2ehi := hb2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
        · linarith only [h0, h5, hc12, hlam, hphi, ht01, u0ehi6]
        · linarith only [h4, h5, hc25, hlam, hphi, u2ehi3]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
        · linarith only [h4, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
          · linarith only [h10, h2, hc24, hlam, hphi, ht01, ht12, u0ehi8]
          · linarith only [h10, h4, hc45, hlam, hphi, ht23, ht34, u2ehi1]

theorem n7l_sBT2_M_LR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.2.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
      · linarith only [h1, h2, hc12, hlam, hphi, u2elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem n7l_sBT2_M_LR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h2ehi := hb2.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
    · linarith only [h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u2ehi4]
    · linarith only [h8, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
    · linarith only [h11, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · linarith only [h11, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
    · linarith only [h14, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
    · linarith only [h14, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h18 | h18
    · linarith only [h18, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · linarith only [h18, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
    · linarith only [h22, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · linarith only [h22, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h25 | h25
    · linarith only [h25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
    · linarith only [h25, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
    · linarith only [h29, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · linarith only [h29, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht23, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h34 | h34
    · linarith only [h34, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
    · linarith only [h34, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h38 | h38
    · linarith only [h38, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · linarith only [h38, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h42 | h42
    · linarith only [h42, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · linarith only [h42, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5elo := hb5.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h5, h9, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h0, h5, h8, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h1, h13, h3, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h1, h13, h15, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h17, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h1, h17, h19, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · linarith only [h19, h5, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h2, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h1, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h25 | h25
          · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
            · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
              · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                · linarith only [h25, h28, h3, hc13, hlam, hphi, ht01, u0ehi9]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h26, h31, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h25, h3, h31, hc23, hc34, hlam, hphi]
                  · linarith only [h25, h3, h30, hc13, hc34, hlam, hphi]
              · linarith only [h2, h27, hc12, hlam, hphi, u2elo0]
            · linarith only [h1, h26, hc12, hlam, hphi, u2elo0]
          · linarith only [h25, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi6, u2elo3]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem n7l_sBT2_M_LR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h2ehi := hb2.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht23, ht34, ht45, p0_1, u2ehi4, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht23, ht34, ht45, p0_1, u2ehi4, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.2.2.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
      · linarith only [h1, h2, hc12, hlam, hphi, u2elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem n7l_sBT2_M_LR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                · linarith only [h6, h7, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h1, h10, h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h1, h13, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                    · linarith only [h13, h6, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h12, h4, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h20, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                · linarith only [h19, h20, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                · linarith only [h1, h19, h23, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi7]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h1, h18, h25, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h0, h2, h25, h27, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                    · linarith only [h18, h19, h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h18, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h2, h3, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h32 | h32
        · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
          · linarith only [h1, h2, h33, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
            · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
              · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
                · linarith only [h0, h37, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                · linarith only [h2, h32, h37, hc12, hc24, hlam, hphi]
              · linarith only [h1, h2, h36, hc12, hc24, hlam, hphi]
            · linarith only [h35, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h1, h32, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h43 | h43
      · rcases m.htr 0 2 5 (by decide) (by decide) with h44 | h44
        · rcases m.htr 0 3 4 (by decide) (by decide) with h45 | h45
          · rcases m.htr 0 3 5 (by decide) (by decide) with h46 | h46
            · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
              · linarith only [h1, h43, h47, hc12, hlam, hphi, ht01, u0ehi8]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                · linarith only [h0, h49, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                · linarith only [h1, h44, h49, hc12, hc23, hlam, hphi]
            · linarith only [h1, h43, h46, hc24, hlam, hphi, ht45, u5elo3]
          · linarith only [h1, h43, h45, hlam]
        · linarith only [h43, h44, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h55 | h55
        · rcases m.htr 0 3 4 (by decide) (by decide) with h56 | h56
          · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
            · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
              · linarith only [h1, h55, h58, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                · linarith only [h0, h60, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                · linarith only [h1, h55, h60, hc12, hc23, hlam, hphi]
            · linarith only [h43, h55, h56, h57, hlam, hphi, u5ehi7, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h64 | h64
            · rcases m.htr 1 2 3 (by decide) (by decide) with h65 | h65
              · linarith only [h1, h55, h65, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h67 | h67
                · linarith only [h0, h67, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                · linarith only [h1, h55, h67, hc12, hc23, hlam, hphi]
            · linarith only [h64, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h55, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h72 | h72
    · rcases m.htr 0 2 4 (by decide) (by decide) with h73 | h73
      · rcases m.htr 0 2 5 (by decide) (by decide) with h74 | h74
        · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
          · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
            · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
              · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h72, h80, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                    · linarith only [h79, h80, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                    · linarith only [h75, h79, h83, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                      · linarith only [h72, h75, h79, h85, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                        · linarith only [h72, h75, h85, h87, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h79, h87, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h78, hc25, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h77, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h76, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h93 | h93
            · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
              · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                  · linarith only [h72, h75, h93, h96, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                    · linarith only [h73, h96, h98, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                    · linarith only [h75, h93, h98, hc23, hc34, hlam, hphi]
                · linarith only [h0, h74, h95, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h94, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h93, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h72, h74, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h105 | h105
        · rcases m.htr 0 3 4 (by decide) (by decide) with h106 | h106
          · linarith only [h106, h72, h73, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h108 | h108
            · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
              · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
                · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                  · linarith only [h106, h108, h111, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
                    · linarith only [h113, h72, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                    · linarith only [h108, h111, h113, h72, h73, hc23, hc34, hlam, hphi]
                · linarith only [h0, h110, hc25, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h109, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h108, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h105, h72, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h120 | h120
      · rcases m.htr 0 2 5 (by decide) (by decide) with h121 | h121
        · rcases m.htr 0 3 4 (by decide) (by decide) with h122 | h122
          · rcases m.htr 0 3 5 (by decide) (by decide) with h123 | h123
            · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
              · linarith only [h0, h124, h72, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h124, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h121, h123, h72, hlam, hphi, u5ehi7, u5elo3]
          · linarith only [h120, h122, h72, hlam]
        · linarith only [h0, h121, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h130 | h130
        · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
          · rcases m.htr 0 3 5 (by decide) (by decide) with h132 | h132
            · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
              · linarith only [h0, h133, h72, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h133, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h120, h130, h131, h132, hlam, hphi, u5ehi7, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h137 | h137
            · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
              · linarith only [h0, h138, h72, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h138, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h137, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h0, h130, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo2]

theorem n7l_sBT2_M_LR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2ehi := hb2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
      · linarith only [h1, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h8 | h8
    · linarith only [h0, h8, hc24, hlam, hphi, u2ehi4]
    · linarith only [h8, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

end R2N4
